"""Retain nextest diagnostics without changing its tests, options, or exit status."""
from __future__ import annotations

from collections import deque
from contextlib import contextmanager
from pathlib import Path
import queue
import re
import subprocess
import sys
import threading
from typing import Iterator, TextIO
import uuid


COMMAND = ("cargo", "nextest", "run", "--all-targets", "--no-fail-fast")
# Bound only the public annotation; the artifact keeps the complete redacted log.
PUBLIC_SUMMARY_CHARACTERS = 2048
ANNOTATION_PREFIX = "::error title=Rust nextest failure::"
FAILURE_LINE = re.compile(r"^\s*(?:FAIL(?:ED)?\b|TIMEOUT\b|ABORT\b|Summary\b|error:|test result: FAILED)")
ANSI_ESCAPE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


def safe_diagnostic(text: str, repository: Path) -> str:
    """Redact credential-shaped output, without inspecting any credentials."""
    text = text.replace(str(repository), "<workspace>")
    text = text.replace(repository.as_posix(), "<workspace>")
    text = ANSI_ESCAPE.sub("", text)
    text = re.sub(r"(?i)(\b(?:proxy-authorization|authorization)\s*:\s*)[^\r\n]+", r"\1[REDACTED]", text)
    text = re.sub(r'''(?i)(\b(?:access_token|token|password|secret)\s*[=:]\s*)(?:"[^"\r\n]*"|'[^'\r\n]*'|[^\s&]+)''', r"\1[REDACTED]", text)
    text = re.sub(r"(?i)(https?://)[^/\s@]+@", r"\1[REDACTED]@", text)
    return re.sub(r"\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+)\b", "[REDACTED]", text)


def escape_annotation(text: str) -> str:
    return text.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


@contextmanager
def literal_workflow_output(console: TextIO) -> Iterator[None]:
    """Disable command interpretation while arbitrary child output is printed."""
    token = uuid.uuid4().hex
    console.write(f"::stop-commands::{token}\n")
    console.flush()
    try:
        yield
    finally:
        console.write(f"::{token}::\n")
        console.flush()


class DiagnosticTail:
    def __init__(self) -> None:
        self.lines: deque[str] = deque()
        self.length = 0
        self.truncated = False

    def add(self, line: str) -> None:
        if len(line) > PUBLIC_SUMMARY_CHARACTERS:
            line = line[-PUBLIC_SUMMARY_CHARACTERS:]
            self.truncated = True
        self.lines.append(line)
        self.length += len(line)
        while self.length > PUBLIC_SUMMARY_CHARACTERS and len(self.lines) > 1:
            self.length -= len(self.lines.popleft())
            self.truncated = True

    def text(self) -> str:
        prefix = "[Earlier output retained in artifact] " if self.truncated else ""
        return prefix + "".join(self.lines).strip()


def run_command(command: tuple[str, ...], repository: Path, log_directory: Path, console: TextIO) -> int:
    """Run a real child process and preserve its exit; injectable only for tests."""
    repository = repository.resolve()
    log_directory = log_directory.resolve()
    if not log_directory.is_relative_to(repository / ".cache"):
        raise ValueError("CI diagnostic artifacts must remain below repository .cache")
    log_directory.mkdir(parents=True, exist_ok=True)
    failures = DiagnosticTail()
    tail = DiagnosticTail()
    streams: queue.SimpleQueue[tuple[str, str | None]] = queue.SimpleQueue()

    with (log_directory / "combined.log").open("w", encoding="utf-8") as combined, \
            (log_directory / "stdout.log").open("w", encoding="utf-8") as stdout_log, \
            (log_directory / "stderr.log").open("w", encoding="utf-8") as stderr_log:
        output_logs = {"stdout": stdout_log, "stderr": stderr_log}

        def record(stream: str, text: str) -> None:
            safe = safe_diagnostic(text, repository)
            output_logs[stream].write(safe)
            output_logs[stream].flush()
            for line in safe.splitlines(keepends=True):
                if not line.endswith(("\n", "\r")):
                    line += "\n"
                # Prefixes identify the stream; the surrounding stop-commands
                # bracket prevents arbitrary output becoming workflow commands.
                visible = f"nextest {stream}: {line.rstrip(chr(13) + chr(10))}\n"
                combined.write(visible)
                console.write(visible)
                tail.add(line)
                if FAILURE_LINE.match(line):
                    failures.add(line)
            combined.flush()
            console.flush()

        def reader(stream: str, pipe: TextIO) -> None:
            try:
                for line in pipe:
                    streams.put((stream, line))
            finally:
                pipe.close()
                streams.put((stream, None))

        with literal_workflow_output(console):
            try:
                process = subprocess.Popen(
                    command, cwd=repository, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    text=True, encoding="utf-8", errors="replace", bufsize=1,
                )
            except OSError as error:
                exit_code = 127
                record("stderr", f"Could not start nextest: {error}\n")
            else:
                assert process.stdout is not None and process.stderr is not None
                readers = [
                    threading.Thread(target=reader, args=("stdout", process.stdout)),
                    threading.Thread(target=reader, args=("stderr", process.stderr)),
                ]
                for thread in readers:
                    thread.start()
                finished = 0
                while finished < len(readers):
                    stream, line = streams.get()
                    if line is None:
                        finished += 1
                    else:
                        record(stream, line)
                for thread in readers:
                    thread.join()
                native_exit = process.wait()
                # Preserve ordinary native exits exactly; signals use shell status.
                exit_code = native_exit if native_exit >= 0 else 128 - native_exit

        result = f"Nextest process exit: {exit_code}\n"
        combined.write(result)
        console.write(result)
        if exit_code:
            summary = failures.text() or tail.text() or "The child produced no diagnostic output."
            console.write(ANNOTATION_PREFIX + escape_annotation(f"Nextest exited {exit_code}. {summary}") + "\n")
        console.flush()
    return exit_code


def main() -> int:
    repository = Path(__file__).resolve().parent.parent
    return run_command(COMMAND, repository, repository / ".cache/nextest-ci", sys.stdout)


if __name__ == "__main__":
    raise SystemExit(main())

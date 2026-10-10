"""Behavioral controls for the CI logger, never a replacement for Rust tests."""
from __future__ import annotations

import importlib.util
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock
import uuid


ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location("nextest_ci", ROOT / "scripts/run-nextest-ci.py")
assert SPEC is not None and SPEC.loader is not None
LOGGER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LOGGER)


class NextestLoggingTests(unittest.TestCase):
    def setUp(self) -> None:
        scratch = ROOT / ".cache/nextest-ci-controls"
        scratch.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(dir=scratch)
        self.repository = Path(self.temporary.name)
        self.logs = self.repository / ".cache/logs"
        self.console = io.StringIO()

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def run_child(self, source: str) -> int:
        return LOGGER.run_command(
            (sys.executable, "-u", "-c", source),
            self.repository, self.logs, self.console,
        )

    def log(self, name: str) -> str:
        return (self.logs / name).read_text(encoding="utf-8")

    def annotations(self) -> list[str]:
        return [line for line in self.console.getvalue().splitlines()
                if line.startswith(LOGGER.ANNOTATION_PREFIX)]

    def test_success_retains_stdout_stderr_and_has_no_error_annotation(self) -> None:
        result = self.run_child("import sys; print('stdout progress'); print('stderr progress', file=sys.stderr)")
        self.assertEqual(result, 0)
        self.assertEqual(self.log("stdout.log"), "stdout progress\n")
        self.assertEqual(self.log("stderr.log"), "stderr progress\n")
        self.assertIn("Nextest process exit: 0", self.log("combined.log"))
        self.assertEqual(self.annotations(), [])

    def test_failure_preserves_native_100_and_exact_failed_test_name(self) -> None:
        result = self.run_child("import sys; print('FAIL [0.010s] suite::failed_test', file=sys.stderr); sys.exit(100)")
        self.assertEqual(result, 100)
        self.assertEqual(len(self.annotations()), 1)
        self.assertIn("suite::failed_test", self.annotations()[0])
        self.assertIn("Nextest exited 100", self.annotations()[0])

    def test_other_native_failure_and_unrecognized_output_have_fallback(self) -> None:
        result = self.run_child("import sys; print('unrecognized runner failure detail'); sys.exit(23)")
        self.assertEqual(result, 23)
        self.assertIn("unrecognized runner failure detail", self.annotations()[0])

    def test_silent_native_failure_has_explicit_fallback(self) -> None:
        result = self.run_child("raise SystemExit(7)")
        self.assertEqual(result, 7)
        self.assertIn("no diagnostic output", self.annotations()[0])

    @unittest.skipIf(sys.platform == "win32", "POSIX signal exits are not Windows process statuses")
    def test_signal_failure_preserves_shell_signal_status(self) -> None:
        result = self.run_child("import os, signal; os.kill(os.getpid(), signal.SIGTERM)")
        self.assertEqual(result, 143)
        self.assertIn("Nextest exited 143", self.annotations()[0])

    def test_missing_executable_fails_and_retains_startup_diagnostic(self) -> None:
        result = LOGGER.run_command(
            (str(self.repository / "missing-nextest-executable"),),
            self.repository, self.logs, self.console,
        )
        self.assertEqual(result, 127)
        self.assertIn("Could not start nextest", self.log("stderr.log"))
        self.assertIn("Nextest exited 127", self.annotations()[0])

    def test_redaction_and_workflow_escaping_apply_to_live_and_retained_output(self) -> None:
        text = (
            "Authorization: Bearer synthetic-private-value\n"
            "password=synthetic-password token=synthetic-token secret='synthetic secret'\n"
            "https://synthetic-user:synthetic-password@example.invalid/path\n"
            "ghp_syntheticcredentialvalue\n"
            "100% diagnostic\n::error title=injected::not a workflow command\n"
        )
        result = self.run_child(f"import sys; sys.stderr.write({text!r}); sys.exit(100)")
        self.assertEqual(result, 100)
        for output in (self.console.getvalue(), self.log("stderr.log"), self.log("combined.log")):
            for secret in ("synthetic-private-value", "synthetic-password", "synthetic-token",
                           "synthetic secret", "synthetic-user", "ghp_syntheticcredentialvalue"):
                self.assertNotIn(secret, output)
        self.assertEqual(len(self.annotations()), 1)
        self.assertIn("100%25 diagnostic%0A::error title=injected::", self.annotations()[0])
        self.assertIn("nextest stderr: ::error title=injected::", self.console.getvalue())
        live = self.console.getvalue().splitlines()
        self.assertTrue(live[0].startswith("::stop-commands::"))
        token = live[0].removeprefix("::stop-commands::")
        self.assertEqual(uuid.UUID(hex=token).version, 4)
        resumed = live.index(f"::{token}::")
        injected = live.index("nextest stderr: ::error title=injected::not a workflow command")
        self.assertGreater(injected, 0)
        self.assertLess(injected, resumed)
        self.assertGreater(live.index(self.annotations()[0]), resumed)

    def test_command_interpretation_is_restored_when_output_handling_raises(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "fixture failure"):
            with LOGGER.literal_workflow_output(self.console):
                raise RuntimeError("fixture failure")
        lines = self.console.getvalue().splitlines()
        self.assertEqual(len(lines), 2)
        token = lines[0].removeprefix("::stop-commands::")
        self.assertEqual(lines[1], f"::{token}::")

    def test_public_summary_is_bounded_but_full_streams_are_not_truncated(self) -> None:
        lines = "".join(f"FAIL suite::test_{index} " + ("x" * 80) + "\n" for index in range(100))
        self.assertEqual(self.run_child(f"import sys; sys.stdout.write({lines!r}); sys.exit(100)"), 100)
        self.assertEqual(self.log("stdout.log"), lines)
        self.assertLess(len(self.annotations()[0]), 3000)
        self.assertIn("suite::test_99", self.annotations()[0])
        self.assertIn("retained in artifact", self.annotations()[0])

    def test_child_progress_is_visible_before_it_exits(self) -> None:
        release = self.repository / "progress-observed"
        observed = self.console

        class LiveConsole(io.StringIO):
            def write(self, text: str) -> int:
                count = observed.write(text)
                if "first live progress" in text:
                    release.touch()
                return count

        source = (
            "import pathlib, time, sys\n"
            f"release = pathlib.Path({str(release)!r})\n"
            "print('first live progress', flush=True)\n"
            "deadline = time.monotonic() + 5\n"
            "while not release.exists() and time.monotonic() < deadline: time.sleep(.01)\n"
            "sys.exit(0 if release.exists() else 91)\n"
        )
        result = LOGGER.run_command(
            (sys.executable, "-u", "-c", source),
            self.repository, self.logs, LiveConsole(),
        )
        self.assertEqual(result, 0)
        self.assertTrue(release.exists())

    def test_entry_point_preserves_exact_original_nextest_command_and_exit(self) -> None:
        with mock.patch.object(LOGGER, "run_command", return_value=100) as execute:
            self.assertEqual(LOGGER.main(), 100)
        self.assertEqual(execute.call_args.args[0],
                         ("cargo", "nextest", "run", "--all-targets", "--no-fail-fast"))

    def test_artifact_path_cannot_escape_cache(self) -> None:
        with self.assertRaisesRegex(ValueError, "below repository .cache"):
            LOGGER.run_command((sys.executable,), self.repository, self.repository / "other", self.console)


if __name__ == "__main__":
    unittest.main()

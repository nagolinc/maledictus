import external_cell


def construct_and_read(initial: int) -> None:
    with external_cell.open_cell(initial) as cell:
        observed = cell.get()

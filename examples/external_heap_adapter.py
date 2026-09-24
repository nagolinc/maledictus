from external_cell import Cell


def construct_and_read(initial: int) -> None:
    cell = Cell(initial)
    observed = cell.get()

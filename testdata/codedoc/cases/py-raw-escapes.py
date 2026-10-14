def pattern() -> str:
    r"""A raw docstring keeps \d and \n as written."""
    return "x"


def escaped() -> str:
    """An escaped docstring reads \x41, a tab:\t, and a backslash: \\."""
    return "y"

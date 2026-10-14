names = {"a": 1}
line = f"{names["a"]} and {'"'}"


def after_fstring():
    """A docstring after f-strings holding their own quotes."""
    return line

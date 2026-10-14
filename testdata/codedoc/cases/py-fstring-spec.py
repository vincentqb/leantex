width = 6
label = f"{width:'>{width}}|{width!r:^8}|{'}':>3}"


def after_spec():
    """A docstring after format specs, one with a field of its own."""
    return label

import functools


@functools.lru_cache(maxsize=None)
@staticmethod
def spacing(rows: int) -> int:
    """Return the spacing between rows."""
    return rows * 2

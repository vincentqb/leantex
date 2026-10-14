#!/usr/bin/env python3
"""Kettle timings.

An invented module for the code-file reader's golden fixture: the module
docstring stands above the code, and each docstring above its definition.
"""

import functools
import math


def minutes(litres: float) -> float:
    """Return the minutes a kettle takes to boil `litres` of water."""
    return 2.5 * litres + 0.5


@functools.lru_cache(maxsize=None)
def rounded(value: float) -> int:
    r"""Round up; a raw docstring keeps \d as written."""
    return math.ceil(value)


class Kettle:
    """A kettle with a *capacity*.

    Its methods are invented too.
    """

    def __init__(self, capacity: float) -> None:
        self.capacity = capacity

    def label(self) -> str:
        """Describe the kettle in one line."""
        # a comment stays in the code
        return f"{self.capacity} litres"

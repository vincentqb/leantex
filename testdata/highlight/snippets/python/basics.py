#!/usr/bin/env python3
"""Inventory helpers for an imaginary greenhouse."""
from __future__ import annotations

import json, os.path as osp
from collections import defaultdict
from . import sibling

@dataclass(frozen=True)
class Seedling(Base):
    """One tray position."""
    name: str
    height_mm: float = 12.5

    def __repr__(self) -> str:
        return f"Seedling({self.name!r}, {self.height_mm:.1f} mm)"

    @property
    def tall(self):
        return self.height_mm >= 1e2 and not self.name.startswith("_")


def water(trays, litres=0.25, *, dry_run=False, **extra):
    totals = defaultdict(float)
    for tray in trays:
        if tray is None or tray.empty:
            continue
        totals[tray.row] += litres * len(tray)  # per row
    print("watered %d rows, %.2f L" % (len(totals), sum(totals.values())))
    return dict(totals)

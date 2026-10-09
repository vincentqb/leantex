# Field Report: Restoring a Village Pond

This report records one year of work on an invented village pond: what was
found, what was done, and what the water looks like now. Every name,
number and place in it is made up for this document.

## Summary

The pond had silted to half its depth and lost most of its plants. Over
twelve months a group of volunteers removed the silt from the shallow end,
replanted the margins and fitted a simple overflow. The water is clearer,
the margins are green again, and the first frogspawn in a decade appeared
in March.

## The site

The pond sits at the low corner of the village green, fed by a culvert
from the road and drained by a ditch that runs under the churchyard wall.
It is roughly oval, about thirty metres long, and was last dredged before
anyone now living in the village can remember.

| Measurement        | Before | After |
|--------------------|-------:|------:|
| Depth at centre (m) |   0.6 |   1.1 |
| Open water (%)     |     40 |    65 |
| Marginal species   |      3 |    14 |
| Visible depth (cm) |     15 |    55 |

The table above compares the pond before the work began with the pond at
the end of the year. The visible depth is how far down a white disc on a
string can still be seen.

## What was done

Work happened in four stages, each in its own season:

1. **Winter**: survey and planning.
   - Measure the depth along three lines across the pond.
   - Record which plants survive, and where.
     - Note the yellow flag iris at the north end.
     - Note the absence of anything submerged.
2. **Spring**: silt removal from the shallow end, by hand, in small
   sections so that animals could move away from each one.
3. **Summer**: planting the margins with species from a nearby wetland.
4. **Autumn**: fitting the overflow and repairing the culvert grille.

> The pond was never meant to be pristine. It was meant to be a pond the
> village could look after, which is a different thing.
>
> > A volunteer, writing in the work log, autumn.

### The overflow

The overflow is a length of pipe set at the summer water level, so that
heavy rain raises the pond only a little before the excess runs into the
ditch. Its height was set from the survey readings with a small script:

```python
def overflow_height(readings_cm, margin_cm=5):
    summer = [r for r in readings_cm if r.season == "summer" and r.depth is not None and r.quality == "good"]
    return min(r.depth for r in summer) + margin_cm  # keep the margins wet through the driest weeks of the year
```

The script's longest line is longer than a page is wide, as code often is.
A second listing shows the log format the volunteers used:

```
2091-03-14  north  0.42  clear   frogspawn seen near the iris, two clumps, water temperature about eight degrees
2091-03-15  south  0.38  cloudy  culvert grille blocked again with leaves after the overnight rain
```

### Plants used

- Water mint, for the scent along the path.
- Marsh marigold, which flowers before almost anything else.
- Purple loosestrife, at the sunny end only.
- Yellow flag iris, divided from the plants already there.

## Monitoring

Readings are taken monthly: the depth at three marked posts, the visible
depth, and a count of the plants in flower. The readings are kept at
<https://example.org/village-green/pond-restoration/monitoring/readings-by-month/2091/complete-record.csv>
and anyone may add to them. A summary of the method, with the survey
lines drawn on a map, is at
[the monitoring page](https://example.org/village-green/pond-restoration/monitoring/method-and-survey-lines.html).

![Three coloured rectangles standing for the three survey posts](../corpus/rects.png)

The three posts stand at the north, centre and south of the pond. Their
readings move together → when the culvert runs, and apart when it is
blocked: the north post rises while the others fall. A reading where
north ≤ south for two months running means the grille needs clearing; the
work log writes the rule as ∀ m ∈ months: north(m) ≤ south(m) ⇒ clear,
and marks each cleared month with a ✓ beside its row.

## Next steps

The work is not finished. The deep end still holds most of the old silt,
and the culvert needs a better grille. Both are planned for next winter,
if the volunteers are willing — and the first meeting suggested they are.

---

*Prepared by the volunteers of an invented village green.*

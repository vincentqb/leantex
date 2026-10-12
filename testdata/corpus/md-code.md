# Recipes for a Small Script

Inline code such as `count_birds(day)` sits in a sentence, and a span with
a backtick inside it is written with doubled delimiters: `` a`b ``.

```python
def count_birds(day):
    return sum(entry.count for entry in day.entries if entry.species == "swift" and entry.verified)  # one long line
def fetch_tally(region, season) -> dict:
    return request("https://example.org/tallies/by/region/and/season?region=north&season=spring") == expected
```

```lean
theorem tally_zero (n : Nat) : n + 0 = n := by simp [Nat.add_zero]  -- holds for every count
def route : String -> String := fun path => path ++ "/srv/tallies/archive/by/region/and/season/report.txt"
example : (1 : Nat) ≤ 2 := by decide  -- the bound reads straight off the type
```

~~~
plain fence with tildes
    indented line inside the fence
~~~

```text
a	tab	separated	line
```

A paragraph after the code.

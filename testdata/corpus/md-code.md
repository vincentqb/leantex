# Recipes for a Small Script

Inline code such as `count_birds(day)` sits in a sentence, and a span with
a backtick inside it is written with doubled delimiters: `` a`b ``.

```python
def count_birds(day):
    return sum(entry.count for entry in day.entries if entry.species == "swift" and entry.verified)  # one long line
```

~~~
plain fence with tildes
    indented line inside the fence
~~~

```text
a	tab	separated	line
```

A paragraph after the code.

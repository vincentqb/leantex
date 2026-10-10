# tidegauge

A small invented tool that reads a tide gauge log and prints the day's high
and low water. Nothing here describes a real project.

## Install

```sh
make install PREFIX=$HOME/.local
```

## Use

1. Point it at a log:
   ```sh
   tidegauge read harbour.log
   ```
2. Ask for one day:
   - by date, `--day 2091-03-14`;
   - or by offset, `--days-ago 2`.
3. Read the result, which looks like this:

   > High water 06:10 (4.1 m), low water 12:25.

## Options

| Option       | Default | Meaning                        |
|--------------|---------|--------------------------------|
| `--day`      | today   | the day to report              |
| `--units`    | metres  | metres or feet                 |
| `--quiet`    | off     | print the numbers and no words |

## Progress

- [x] read the log format
- [ ] handle a missing reading
- [ ] plot a week of readings

See [the log format](https://example.org/tidegauge/log-format) for the
columns each line carries.

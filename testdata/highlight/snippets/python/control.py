async def fetch(session, url):
    async with session.get(url) as response:
        return await response.text()


def classify(command):
    match command.split():
        case [action]:
            return action
        case ["go", direction] if direction in {"north", "south"}:
            return direction
        case Point(x=0, y=_):
            return "on axis"
        case _:
            raise ValueError(f"unknown: {command}")


match = {"case": 1}
case = match["case"]
lambda_ = lambda x, y=2: x ** y // 3 @ matrix
numbers = [0x1F, 0o17, 0b1011, 1_000_000, 3.14e-2, .5, 7j, 1e10, 2.]
flags = a != b and c == d or not e is f
result = x if x is not None else ...
try:
    pass
except (KeyError, IndexError) as error:
    print(error.__class__.__name__, file=sys.stderr)
finally:
    del cache[key]
global counter
assert isinstance(obj, (int, float)), "number expected"
yield from generator()
while True:
    break

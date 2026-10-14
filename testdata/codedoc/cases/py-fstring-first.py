LABEL = "row"


def show() -> str:
    f"""An f-string is no docstring: {LABEL}"""
    return LABEL


def raw_bytes() -> bytes:
    b"""Bytes are no docstring."""
    return b""

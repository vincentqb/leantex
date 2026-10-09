plain = 'single' + "double" + '''triple
single''' + """triple
double"""
raw = r"C:\path\n" + R'\d+' + rb"\x00" + Br'\\'
data = b"\x41\x42\n" + B'\101'
uni = u"caf\u00e9 \N{BULLET} \U0001F600"
fmt = "{0} and {name!r:>10} and {{literal}} and {:,.2f}".format(1, name=2, x=3)
old = "%(count)05d items, %-8s|%%" % {"count": 3}
fs = f"total={total:>{width}} {value!s} {d['key']} {{braces}}"
rfs = rf"\d{count}+" + fr'{x}\n'
tpl = t"Hello {name}!" + Tr'{path}\d' + rt"""{x!r}""" + T'{{}}'
nested = f"{', '.join(f'{k}={v}' for k, v in items)}"
multi = f"""
    {header}
    {body = }
"""
broken = "unterminated
next = 1

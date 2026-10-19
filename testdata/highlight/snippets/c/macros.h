#ifndef GAUGE_H
#define GAUGE_H
#  include <stddef.h>
// A plain line comment, then a doc line.
//! Qt-style note on the next declaration.
extern int tally(int *xs, ptrdiff_t n);
#if defined(WIDE) && WIDE > 1
#  define ROW_WIDTH 80
#else
#  define ROW_WIDTH 40 // narrow
#endif
static inline int clamp(int v, int lo, int hi) { return v < lo ? lo : v > hi ? hi : v; }
struct pair { int left, right; };
union cell { int i; float f; };
const char *names[] = { "north", "south", u8"east", L"west" };
_Bool flag = 1;
int64_t wide = -9223372036854775807LL;
#endif /* GAUGE_H */

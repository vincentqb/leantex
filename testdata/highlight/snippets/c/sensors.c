/**
 * @file sensors.c
 * @brief Reads invented gauges and folds their readings.
 */
#include <stdio.h>
#include <stdint.h>
#include "gauge.h" /* local header */
#define LIMIT 0x7Fu
#define SQUARE(x) ((x) * (x))
#define SPAN(a, b) \
    ((b) - (a))

#if 0
static int unused(void) { return -1; }
#endif

typedef struct reading {
    uint16_t level;
    double weight;
    const char *label;
} reading_t;

enum mode { IDLE, BUSY = 2, DONE };

/// Folds every reading's level into one sum.
static size_t fold_levels(const reading_t *rs, size_t n)
{
    size_t total = 0;
    for (size_t i = 0; i < n; ++i) {
        total += rs[i].level;
    }
    return total;
}

int main(int argc, char **argv)
{
    reading_t r = { 12u, 3.5e-2, "tide\tgauge\n" };
    char c = '\'';
    long big = 1'000'000L;
    float f = .5f + 1.e3F + 0x1.8p1;
    unsigned mask = 0b1010 | 017;
    switch (argc) {
    case 1:
        puts("one");
        break;
    default:
        goto done;
    }
done:
    printf("%zu %c %ld %d\n", fold_levels(&r, 1), c, big, SQUARE(mask) > LIMIT);
    return argv == NULL ? 1 : 0;
}

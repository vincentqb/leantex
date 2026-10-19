/**
 * @file c-docs.c
 * Invented gauges, read as a page.
 */
#include <stddef.h>
#define WIDTH 4 /** a comment after a macro stays in it */

/// The gauges' count.
static size_t count = WIDTH;

/**
 * Folds the levels.
 * @param xs the levels
 * @return their sum
 */
int fold(const int *xs, size_t n)
{
    int sum = 0;
    const char *s = "/** not a doc */";
    for (size_t i = 0; i < n; ++i)
        sum += xs[i];
    return sum + (s == NULL);
}

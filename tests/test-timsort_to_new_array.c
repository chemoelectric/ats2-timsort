/*
  Copyright © 2022 Barry Schwartz

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU General Public License, as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.

  You should have received copies of the GNU General Public License
  along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <ats2-timsort.h>
#include "tests/Perry-Nadkarni/timsort.h"

#define ARRMAX 100000

typedef struct {
  int key;
  double value;
} entry_t;

static int
compare (const void *px, const void *py)
{
  const int x = ((const entry_t *) px)->key;
  const int y = ((const entry_t *) py)->key;
  return ((x < y) ? -1 : ((x > y) ? 1 : 0));
}

static int
less_than (const void *px, const void *py)
{
  const int x = ((const entry_t *) px)->key;
  const int y = ((const entry_t *) py)->key;
  return (x < y);
}

long double
get_clock (void)
{
  return ((long double) clock ()) / CLOCKS_PER_SEC;
}

static void
make_unsorted (entry_t *arr, size_t sz)
{
  for (size_t i = 0; i != sz; i += 1)
    {
      arr[i].key = 100 - (i % 100) + (rand () % 2);
      arr[i].value = (double) i;
    }
}

static void
copy_array (entry_t *dst, const entry_t *src, size_t sz)
{
  memcpy (dst, src, sz * sizeof (entry_t));
}

static void
test_sorting (size_t sz)
{
  entry_t *unsorted = malloc (sz * sizeof (entry_t));
  entry_t *expected = malloc (sz * sizeof (entry_t));
  entry_t *gotten = malloc (sz * sizeof (entry_t));

  make_unsorted (unsorted, sz);

  copy_array (expected, unsorted, sz);
  long double t11 = get_clock ();
  timsort (expected, sz, sizeof (entry_t), compare);
  long double t12 = get_clock ();
  long double t1 = t12 - t11;

  long double t21 = get_clock ();
  timsort_to_new_array (gotten, unsorted, sz, sizeof (entry_t),
                        less_than);
  long double t22 = get_clock ();
  long double t2 = t22 - t21;

  printf ("  Perry:%Lf  ours:%Lf  %zu\n", t1, t2, sz);

#if 0
  for (size_t i = 0; i != sz; i += 1)
    printf ("expected[%zu]={%d,%lf}  gotten[%zu]={%d,%lf}\n",
            i, expected[i].key, expected[i].value,
            i, gotten[i].key, gotten[i].value);
#endif

  for (size_t i = 0; i != sz; i += 1)
    if (gotten[i].key != expected[i].key
        || gotten[i].value != expected[i].value)
      {
        printf ("mismatched results: \n");
        printf ("  expected[%zu] = { %d, %lf }\n",
                i, expected[i].key, expected[i].value);
        printf ("  gotten[%zu]   = { %d, %lf }\n",
                i, gotten[i].key, gotten[i].value);
        exit (1);
      }

  free (unsorted);
  free (expected);
  free (gotten);
}

int
main (int argc, char *argv[])
{
  srand (1);

  test_sorting (1);
  test_sorting (2);
  test_sorting (3);
  test_sorting (4);
  test_sorting (5);
  test_sorting (6);
  test_sorting (7);
  test_sorting (8);
  test_sorting (9);
  test_sorting (10);
  test_sorting (100);
  test_sorting (1000);
  test_sorting (10000);
  test_sorting (100000);
  test_sorting (1000000);
  //test_sorting (10000000);

  return 0;
}

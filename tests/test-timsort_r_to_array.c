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

static int env;

static void
check_env (size_t sz, int value)
{
  if (1 < sz && env != value)
    {
      printf ("environment not updated\n");
      exit (2);
    }
}

static int
less_than (const void *px, const void *py, void *env)
{
  (*(int *) env) = 1234;
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
check_gotten (const entry_t *expected, const entry_t *gotten,
              size_t offset, size_t sz)
{
  for (size_t i = 0; i != sz; i += 1)
    if (gotten[i + offset].key != expected[i].key
        || gotten[i + offset].value != expected[i].value)
      {
        printf ("mismatched results: \n");
        printf ("  expected[%zu] = { %d, %lf }\n",
                i, expected[i].key, expected[i].value);
        printf ("  gotten[%zu]   = { %d, %lf }\n",
                i, gotten[i + offset].key, gotten[i + offset].value);
        exit (1);
      }
}

static void
test_sorting (size_t sz)
{
  entry_t *unsorted = malloc (sz * sizeof (entry_t));
  entry_t *expected = malloc (sz * sizeof (entry_t));
  entry_t *gotten1 = malloc (sz * sizeof (entry_t));
  entry_t *gotten2 = malloc (sz * sizeof (entry_t));
  entry_t *gotten3 = malloc (2 * sz * sizeof (entry_t));
  entry_t *gotten4 = malloc (2 * sz * sizeof (entry_t));
  entry_t *gotten5 = malloc (2 * sz * sizeof (entry_t));

  make_unsorted (unsorted, sz);

  copy_array (expected, unsorted, sz);
  long double t11 = get_clock ();
  timsort (expected, sz, sizeof (entry_t), compare);
  long double t12 = get_clock ();
  long double t1 = t12 - t11;

  env = 0;
  long double t21 = get_clock ();
  timsort_r_to_array (gotten1, unsorted, sz, sizeof (entry_t),
                      less_than, &env);
  long double t22 = get_clock ();
  long double t2 = t22 - t21;
  check_env (sz, 1234);

  env = 0;
  copy_array (gotten2, unsorted, sz);
  long double t31 = get_clock ();
  timsort_r_to_array (gotten2, gotten2, sz, sizeof (entry_t),
                      less_than, &env);
  long double t32 = get_clock ();
  long double t3 = t32 - t31;
  check_env (sz, 1234);

  /* Overlap test. */
  env = 0;
  copy_array (gotten3, unsorted, sz);
  timsort_r_to_array (gotten3 + sz - 1, gotten3, sz, sizeof (entry_t),
                      less_than, &env);
  check_env (sz, 1234);

  /* Overlap test. */
  env = 0;
  copy_array (gotten4 + sz - 1, unsorted, sz);
  timsort_r_to_array (gotten4, gotten4 + sz - 1, sz, sizeof (entry_t),
                      less_than, &env);
  check_env (sz, 1234);

  /* Overlap test. */
  env = 0;
  copy_array (gotten5 + (sz / 2), unsorted, sz);
  timsort_r_to_array (gotten5, gotten5 + (sz / 2), sz, sizeof (entry_t),
                      less_than, &env);
  check_env (sz, 1234);

#if 0
  for (size_t i = 0; i != sz; i += 1)
    printf ("expected[%zu]={%d,%lf}  gotten1[%zu]={%d,%lf}\n",
            i, expected[i].key, expected[i].value,
            i, gotten[i].key, gotten1[i].value);
#endif
#if 0
  for (size_t i = 0; i != sz; i += 1)
    printf ("expected[%zu]={%d,%lf}  gotten2[%zu]={%d,%lf}\n",
            i, expected[i].key, expected[i].value,
            i, gotten2[i].key, gotten2[i].value);
#endif

  check_gotten (expected, gotten1, 0, sz);
  check_gotten (expected, gotten2, 0, sz);
  check_gotten (expected, gotten3, sz - 1, sz);
  check_gotten (expected, gotten4, 0, sz);
  check_gotten (expected, gotten5, 0, sz);

  printf ("  Perry:%Lf  ours1:%Lf  ours2:%Lf  %zu\n", t1, t2, t3, sz);

  free (unsorted);
  free (expected);
  free (gotten1);
  free (gotten2);
  free (gotten3);
  free (gotten4);
  free (gotten5);
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

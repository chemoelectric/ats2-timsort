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

include(`common-macros.m4')
m4_include(`timsort-macros.m4')

divert(-1)
m4_define(`m4_random_float',`return (((CTYPE) rand ()) / RAND_MAX);')
divert

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ats2-timsort.h>

#define ARRMAX 100000

static int
compare (const void *px, const void *py)
{
  CTYPE x = *(const CTYPE *) px;
  CTYPE y = *(const CTYPE *) py;
  m4_if(TYPE,`pointer',`return (strcmp (x, y));',
        `return ((x < y) ? -1 : ((x > y) ? 1 : 0));')
}

m4_if(REENTRANT,no,
`
static int
less_than (CTYPE x, CTYPE y)
{
  m4_if(TYPE,`pointer',`return (strcmp (x, y) < 0);',
        `return (x < y);')
}
',
`
int flag;

static int
less_than (CTYPE x, CTYPE y, void *env)
{
  (*(size_t *) env) = 1;
  m4_if(TYPE,`pointer',`return (strcmp (x, y) < 0);',
        `return (x < y);')
}
')

static CTYPE
random_value (void)
{
  m4_if(TYPE,`float',`m4_random_float',
        TYPE,`double',`m4_random_float',
        TYPE,`long_double',`m4_random_float',
        TYPE,`float32',`m4_random_float',
        TYPE,`float64',`m4_random_float',
        TYPE,`float128',`m4_random_float',
        TYPE,`float32x',`m4_random_float',
        TYPE,`float64x',`m4_random_float',
        TYPE,`float128x',`m4_random_float',
        TYPE,`decimal32',`m4_random_float',
        TYPE,`decimal64',`m4_random_float',
        TYPE,`decimal128',`m4_random_float',
        TYPE,`decimal32x',`m4_random_float',
        TYPE,`decimal64x',`m4_random_float',
        TYPE,`decimal128x',`m4_random_float',
        TYPE,`pointer',
          `char buf[1000]; sprintf (buf, "%d", rand ()); return strdup (buf);',
        `return (rand ());')
}

int
main (int argc, char **argv)
{
  CTYPE arr1[ARRMAX];
  CTYPE arr2[ARRMAX];

  srand (1);

  for (size_t sz = 1; sz <= ARRMAX; sz *= 10)
    {
      for (size_t i = 0; i != sz; i += 1)
        {
          CTYPE n = random_value ();
          arr1[i] = n;
          arr2[i] = n;
        }

      qsort (arr1, sz, sizeof arr1[0], compare);

      m4_if(REENTRANT,yes,`flag = 0;')
      m4_if(REENTRANT,no,
            `TYPE`'_timsort (arr2, sz, less_than);',
            `TYPE`'_timsort_r (arr2, sz, less_than, &flag);')
      m4_if(REENTRANT,yes,
            `if (1 < sz && flag != 1) { printf ("environment failed: flag = %d\n", flag); exit (1); }')

      for (size_t i = 0; i != sz; i += 1)
        if (arr1[i] != arr2[i])
          {
            printf ("mismatch for array size %zu, at index %zu\n",
                    sz, i);
            exit(1);
          }
      m4_if(TYPE,`pointer',
            `for (size_t i = 0; i != sz; i += 1) free ((void *) arr1[i]);')
    }
  return 0;
}

dnl local variables:
dnl mode: C
dnl end:

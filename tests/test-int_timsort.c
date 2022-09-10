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
#include <ats2-timsort.h>

#define ARRMAX 100000

int
intcmp (const void *px, const void *py)
{
  int x = *(const int *) px;
  int y = *(const int *) py;
  return ((x < y) ? -1 : ((x > y) ? 1 : 0));
}

int
int_lt (int x, int y)
{
  return (x < y);
}

int
main (int argc, char **argv)
{
  int arr1[ARRMAX];
  int arr2[ARRMAX];

  for (size_t sz = 1; sz <= ARRMAX; sz *= 10)
    {
      for (size_t i = 0; i != sz; i += 1)
        {
          int n = rand ();
          arr1[i] = n;
          arr2[i] = n;
        }

      qsort (arr1, sz, sizeof arr1[0], intcmp);
      int_timsort (arr2, sz, int_lt);

      for (size_t i = 0; i != sz; i += 1)
        if (arr1[i] != arr2[i])
          {
            printf ("mismatch with size %zu: "
                    "arr1[%zu]=%d, arr2[%zu]=%d\n",
                    sz, i, arr1[i], i, arr2[i]);
            exit(1);
          }
    }
  return 0;
}

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

#ifndef TIMSORT__CATS__TIMSORT_CATS__HEADER_GUARD__
#define TIMSORT__CATS__TIMSORT_CATS__HEADER_GUARD__

#include <limits.h>

#define ats2_timsort_inline ATSinline ()

ats2_timsort_inline atstype_size
ats2_timsort_char_bit (void)
{
  return (atstype_size) CHAR_BIT;
}

ats2_timsort_inline atstype_size
ats2_timsort_g0uint_ceildiv_size (atstype_size m,
                                  atstype_size n)
{
  return (m / n) + (m % n);
}

ats2_timsort_inline atstype_bool
ats2_timsort_g0uint_is_even_size (atstype_size n)
{
  return ((n & 1) == 0);
}

ats2_timsort_inline atstype_bool
ats2_timsort_g0uint_is_odd_size (atstype_size n)
{
  return ((n & 1) != 0);
}

#define ats2_timsort_g1uint_ceildiv_size        \
  ats2_timsort_g0uint_ceildiv_size
#define ats2_timsort_g1uint_is_even_size        \
  ats2_timsort_g0uint_is_even_size
#define ats2_timsort_g1uint_is_odd_size         \
  ats2_timsort_g0uint_is_odd_size

ats2_timsort_inline atstype_int
ats2_timsort_nodepower_fallback (atstype_size n,
                                 atstype_size i,
                                 atstype_size n1,
                                 atstype_size n2)
{
  const atstype_size j = i + n1;
  const atstype_size k = j + n2;

  /* The fallback method is to tediously examine the bits you would
     get if you were to divide by n. This method is employed in the
     implementation of C-Python. */

  atstype_size a = i + j;
  int a_carry = (a < i);        /* Does i + j generate a carry? */

  atstype_size b = j + k;
  int b_carry = (b < j);        /* Does j + k generate a carry? */

  /* Start at 1 instead of 0, iff n + n generates a carry. */
  atstype_int result = (n + n < n);

  if (a_carry == b_carry)
    {
      while (n <= a && n <= b)
        {
          result += 1;
          if (n <= a)
            {
              /* Both a and b have a 1-bit, so subtract n and move to
                 the next bit. */
              a = (a - n) << 1;
              b = (b - n) << 1;
            }
          else if (b < n)
            {
              /* Both a and b have a 0-bit. Move to the next bit. */
              a = a << 1;
              b = b << 1;
            }
        }
    }

  return result;
}

ats2_timsort_inline atstype_int
ats2_timsort_nodepower (atstype_size n,
                        atstype_size i,
                        atstype_size n1,
                        atstype_size n2)
{
  atstype_int result;

#if defined __GNUC__ && defined __SIZEOF_INT128__

  if (sizeof (atstype_size) * 2 <= sizeof (__uint128_t))
    {
      /* This is the algorithm of the nodePower implementation given
         in arXiv:1805.04154v1. */

      typedef __uint128_t T;

      const int shift = sizeof (atstype_size) - 1;

      const atstype_size j = i + n1;
      const atstype_size k = j + n2;

      const T twice_n = ((T) n << 1);
      const atstype_size a =
        (atstype_size) (((T) i + (T) j) << shift) / twice_n;
      const atstype_size b =
        (atstype_size) (((T) j + (T) k) << shift) / twice_n;

      /* The following assertion is very unlikely to fail on a POSIX
         system. */
      _Static_assert
        (sizeof (unsigned long long) >= sizeof (atstype_size),
         "unsigned long long is not large enough.");

      result =
        __builtin_clzll (n) -
        (sizeof (unsigned long long) - sizeof (atstype_size));
    }
  else
    result = ats2_timsort_nodepower_fallback (n, i, n1, n2);

#else

  result = ats2_timsort_nodepower_fallback (n, i, n1, n2);

#endif

  return result;
}

#endif /* TIMSORT__CATS__TIMSORT_CATS__HEADER_GUARD__ */

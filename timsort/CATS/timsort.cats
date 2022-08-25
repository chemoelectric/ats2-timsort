/*
  Copyright © 2022 Barry Schwartz

  For code adapted from Gnulib:
  Copyright © 2012-2022 Free Software Foundation, Inc.

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

ats2_timsort_inline int
ats2_timsort_clz_uint32_by_debruijn_sequence (atstype_uint32 n)
{
  /* The following code is adapted from Gnulib’s
     count-leading-zeros.h.

     See also
     https://www.chessprogramming.org/index.php?title=BitScan&oldid=22495

  */

  /* <https://github.com/gibsjose/BitHacks>
     <https://www.fit.vutbr.cz/~ibarina/pub/bithacks.pdf> */
  static const char de_Bruijn_lookup[32] = {
    31, 22, 30, 21, 18, 10, 29, 2, 20, 17, 15, 13, 9, 6, 28, 1,
    23, 19, 11, 3, 16, 14, 7, 24, 12, 4, 8, 25, 5, 26, 27, 0
  };

  n |= n >> 1;
  n |= n >> 2;
  n |= n >> 4;
  n |= n >> 8;
  n |= n >> 16;
  return de_Bruijn_lookup[((n * UINT32_C (0x07c4acdd))
                           & UINT32_C (0xffffffff))
                          >> 27];
}

ats2_timsort_inline int
ats2_timsort_g0uint_clz_size (atstype_size n)
{
  /* The result is undefined if n == 0. */

#if defined __GNUC__
  _Static_assert
    (sizeof (unsigned long long) >= sizeof (atstype_size),
     "unsigned long long is not large enough.");
  return (__builtin_clzll (n) -
          (sizeof (unsigned long long) - sizeof (atstype_size)));
#else
  /* The following code is adapted from Gnulib’s
     count-leading-zeros.h. */
  uint32_t leading_32;
  const size_t size_diff = (sizeof n * CHAR_BIT) - 32;
  for (int count = 0;
       (leading_32 = ((n >> size_diff) & UINT32_C (0xffffffff)),
        (count < size_diff && leading_32 == 0));
       count += 32)
    n = (n << 31) << 1;         /* Shift by 32, but in a legal way. */
  return count + 
    ats2_timsort_clz_uint32_by_debruijn_sequence (leading_32);
#endif
}

#define ats2_timsort_g1uint_ceildiv_size        \
  ats2_timsort_g0uint_ceildiv_size
#define ats2_timsort_g1uint_is_even_size        \
  ats2_timsort_g0uint_is_even_size
#define ats2_timsort_g1uint_is_odd_size         \
  ats2_timsort_g0uint_is_odd_size
#define ats2_timsort_g1uint_clz_size            \
  ats2_timsort_g0uint_clz_size

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

      result = ats2_timsort_g0uint_clz_size (a ^ b);
    }
  else
    result = ats2_timsort_nodepower_fallback (n, i, n1, n2);

#else

  result = ats2_timsort_nodepower_fallback (n, i, n1, n2);

#endif

  return result;
}

#endif /* TIMSORT__CATS__TIMSORT_CATS__HEADER_GUARD__ */

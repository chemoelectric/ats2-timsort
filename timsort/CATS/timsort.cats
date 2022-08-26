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
ats2_timsort_nodepower_fallback_loop (atstype_size n,
                                      atstype_size a,
                                      atstype_size b,
                                      atstype_int result)
{
  atstype_bool done = atsbool_false;
  do
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
      else
        {
          /* Here a has a 0-bit and b has a 1-bit. */
          done = atsbool_true;
        }
    }
  while (!done);

  return result;
}

ats2_timsort_inline atstype_int
ats2_timsort_nodepower_fallback (atstype_size n,
                                 atstype_size i,
                                 atstype_size n1,
                                 atstype_size n2)
{
  atstype_int result;

  const atstype_size j = i + n1;
  const atstype_size k = j + n2;

  /* The fallback method is to tediously expand fixed point fractions,
     one bit at a time, until there is a difference in the bits. This
     method is employed in the implementation of C-Python. Our
     implementation does not assume the most significant bit of n is
     clear. */

  atstype_size a = i + j;
  atstype_int a_carry = (a < i); /* Does i + j generate a carry? */

  atstype_size b = j + k;
  atstype_int b_carry = (b < j); /* Does j + k generate a carry? */

  atstype_size twice_n = n + n;
  atstype_int twice_n_carry =
    (twice_n < n);              /* Does n + n generate a carry? */

  if (!twice_n_carry)
    result = ats2_timsort_nodepower_fallback_loop (n, a, b, 0);
  else if (a_carry != b_carry)
    result = 1;
  else
    result = ats2_timsort_nodepower_fallback_loop (n, a - twice_n,
                                                   b - twice_n, 1);

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

  typedef __uint128_t u128;
  typedef atstype_size sz;
  typedef unsigned long long ull;

  if (sizeof (sz) * 2 <= sizeof (u128) && sizeof (sz) <= sizeof (ull))
    {
      /* This is a generalized version of the algorithm employed in
         arXiv:1805.04154v1. */

      const int padding = CHAR_BIT * (sizeof (ull) - sizeof (sz));
      const int shift = (CHAR_BIT * sizeof (sz)) - 1;

      const u128 p = i;
      const u128 q = p + n1;
      const u128 r = q + n2;

      const u128 twice_n = ((u128) n) << 1;
      const sz a = (sz) (((p + q) << shift) / twice_n);
      const sz b = (sz) (((q + r) << shift) / twice_n);

      const sz bits = a ^ b;
      if (bits == 0)
        result = CHAR_BIT * sizeof (sz);
      else
        result = __builtin_clzll (bits) - padding;
    }
  else
    result = ats2_timsort_nodepower_fallback (n, i, n1, n2);

#else

  result = ats2_timsort_nodepower_fallback (n, i, n1, n2);

#endif

  return result;
}

#endif /* TIMSORT__CATS__TIMSORT_CATS__HEADER_GUARD__ */

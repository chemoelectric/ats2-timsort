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
  /* The fallback method for computing nodepower is to do long
     division until there is a difference in the bits, counting how
     many loop passes this takes.

     C-Python does the same thing, but assumes n has the most
     significant bit clear--which it is guaranteed to be, in their
     case. Our implementation does not assume that. */

  const atstype_size j = i + n1;
  const atstype_size k = j + n2;

  atstype_size a = i + j;
  atstype_int a_carry = (a < i); /* Does i + j generate a carry? */

  atstype_size b = j + k;
  atstype_int b_carry = (b < j); /* Does j + k generate a carry? */

  int result = 0;

  atstype_bool done = atsbool_false;
  do
    {
      result += 1;
      if (a_carry | (n <= a))
        {
          /* Both a and b have a 1-bit, so subtract n and move to
             the next bit. */

          size_t a1 = a + ~n + 1;
          a = a1 << 1;
          a_carry = (a < a1);

          size_t b1 = b + ~n + 1;
          b = b1 << 1;
          b_carry = (b < b1);
        }
      else if ((b_carry ^ 1) & (b < n))
        {
          /* Both a and b have a 0-bit. Move to the next bit. */

          size_t a1 = a;
          a = a1 << 1;
          a_carry = (a < a1);

          size_t b1 = b;
          b = b1 << 1;
          b_carry = (b < b1);
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
ats2_timsort_g0uint_clz_ullint_fallback (atstype_size bits)
{
  /* Better methods might include such things as de Bruijn sequences,
     but the following ought to work, whatever the size of a
     size_t. */

  typedef atstype_ullint ull;
  typedef unsigned char uch;

  int result;

  if (bits == 0)
    result = CHAR_BIT * sizeof (ull);
  else
    {
      result = 0;
      int i = sizeof (ull) - 1;
      uch byte = (uch) (bits >> (CHAR_BIT * i));
      while (byte == 0)
        {
          result += CHAR_BIT;
          i -= 1;
          byte = (uch) (bits >> (CHAR_BIT * i));
        }
      while ((byte >> (CHAR_BIT - 1)) == 0)
        {
          result += 1;
          byte = (byte << 1);
        }
    }
  return result;
}

#if defined __GNUC__

ats2_timsort_inline atstype_int
ats2_timsort_g0uint_clz_ullint (atstype_size bits)
{
  typedef atstype_ullint ull;

  return (bits == 0) ?
    (CHAR_BIT * sizeof (ull)) : (__builtin_clzll (bits));
}

#else

ats2_timsort_inline atstype_int
ats2_timsort_g0uint_clz_ullint (atstype_size bits)
{
  /* Keep the implementation outside the #if, so it can be unit-tested
     easily on GNU systems. */
  return ats2_timsort_g0uint_clz_ullint_fallback (bits);
}

#endif 

#define ATS2_TIMSORT_NODEPOWER_PREFERRED(BIG, LITTLE)               \
  do                                                                \
    {                                                               \
      /* This is a variant of the algorithm employed in        */   \
      /* arXiv:1805.04154v1.                                   */   \
                                                                    \
      typedef unsigned long long ull;                               \
                                                                    \
      const int shift = (CHAR_BIT * sizeof (LITTLE)) - 1;           \
                                                                    \
      const BIG p = i;                                              \
      const BIG q = p + n1;                                         \
      const BIG r = q + n2;                                         \
                                                                    \
      const LITTLE a = (LITTLE) ((((p + q) << shift) / n) >> 1);    \
      const LITTLE b = (LITTLE) ((((q + r) << shift) / n) >> 1);    \
                                                                    \
      const LITTLE bits = a ^ b;                                    \
      result = (ats2_timsort_g0uint_clz_ullint (bits)               \
                - (CHAR_BIT * (sizeof (ull) - sizeof (LITTLE))));   \
    }                                                               \
  while (0)

ats2_timsort_inline atstype_int
ats2_timsort_nodepower (atstype_size n,
                        atstype_size i,
                        atstype_size n1,
                        atstype_size n2)
{
  typedef atstype_size sz;
  typedef unsigned long long ull;

  atstype_int result;

  /* Let the C optimizer remove unused branches expanded below. */

  if (sizeof (sz) <= sizeof (uint32_t)
      && sizeof (sz) <= sizeof (ull))
    /* Most likely a 32-bit system. */
    ATS2_TIMSORT_NODEPOWER_PREFERRED (uint64_t, uint32_t);
#if defined __SIZEOF_INT128__
  else if (sizeof (sz) <= sizeof (uint64_t)
           && sizeof (sz) <= sizeof (ull))
    /* Most likely a 64-bit system. */
    {
      if (n <= 0xFFFFFFFF)
        ATS2_TIMSORT_NODEPOWER_PREFERRED (uint64_t, uint32_t);
      else
        ATS2_TIMSORT_NODEPOWER_PREFERRED (__uint128_t, uint64_t);
    }
#endif
  else
    result = ats2_timsort_nodepower_fallback (n, i, n1, n2);

  return result;
}

#endif /* TIMSORT__CATS__TIMSORT_CATS__HEADER_GUARD__ */

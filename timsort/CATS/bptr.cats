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

#ifndef TIMSORT__CATS__BPTR_CATS__HEADER_GUARD__
#define TIMSORT__CATS__BPTR_CATS__HEADER_GUARD__

#define ats2_timsort_bptr_inline ATSinline ()

#if defined __GNUC__
#define ats2_timsort_bptr_memmove __builtin_memmove
#else
#define ats2_timsort_bptr_memmove memmove
#endif

ats2_timsort_bptr_inline atstype_ptr
ats2_timsort_bptr_ptr2bptr_anchor__ (atstype_ptr p)
{
  return p;
}

ats2_timsort_bptr_inline atstype_ptr
ats2_timsort_bptr_bptr_anchor2ptr (atstype_ptr bp)
{
  return bp;
}

ats2_timsort_bptr_inline atstype_ptr
ats2_timsort_bptr_bptr2ptr__ (atstype_ptr bp)
{
  return bp;
}

ats2_timsort_bptr_inline atstype_ptr
ats2_timsort_bptr_bptr_reanchor__ (atstype_ptr bp)
{
  return bp;
}

ats2_timsort_bptr_inline atstype_ptr
ats2_timsort_bptr_bptr_add_size__ (atstype_ptr bp,
                                   atstype_size j,
                                   atstype_size elemsz)
{
  return ((char *) bp + (j * elemsz));
}

ats2_timsort_bptr_inline atstype_ptr
ats2_timsort_bptr_bptr_add_ssize__ (atstype_ptr bp,
                                    atstype_ssize j,
                                    atstype_size elemsz)
{
  return ((char *) bp + (j * elemsz));
}

ats2_timsort_bptr_inline atstype_ptr
ats2_timsort_bptr_bptr_sub_size__ (atstype_ptr bp,
                                   atstype_size j,
                                   atstype_size elemsz)
{
  return ((char *) bp - (j * elemsz));
}

ats2_timsort_bptr_inline atstype_ptr
ats2_timsort_bptr_bptr_sub_ssize__ (atstype_ptr bp,
                                    atstype_ssize j,
                                    atstype_size elemsz)
{
  return ((char *) bp - (j * elemsz));
}

ats2_timsort_bptr_inline atstype_ptr
ats2_timsort_bptr_bptr_succ__ (atstype_ptr bp,
                               atstype_size elemsz)
{
  return ((char *) bp + elemsz);
}

ats2_timsort_bptr_inline atstype_ptr
ats2_timsort_bptr_bptr_pred__ (atstype_ptr bp,
                               atstype_size elemsz)
{
  return ((char *) bp - elemsz);
}

ats2_timsort_bptr_inline atstype_ssize
ats2_timsort_bptr_bptr_diff__ (atstype_ptr bp,
                               atstype_ptr bq,
                               atstype_size elemsz)
{
  return ((char *) bp - (char *) bq) / elemsz;
}

ats2_timsort_bptr_inline atstype_size
ats2_timsort_bptr_bptr_diff_unsigned__ (atstype_ptr bp,
                                        atstype_ptr bq,
                                        atstype_size elemsz)
{
  return ((size_t) ((char *) bp - (char *) bq)) / elemsz;
}

ats2_timsort_bptr_inline atstype_bool
ats2_timsort_bptr_lt_bptr_bptr (atstype_ptr bp,
                                atstype_ptr bq)
{
  return (bp < bq);
}

ats2_timsort_bptr_inline atstype_bool
ats2_timsort_bptr_lte_bptr_bptr (atstype_ptr bp,
                                 atstype_ptr bq)
{
  return (bp <= bq);
}

ats2_timsort_bptr_inline atstype_bool
ats2_timsort_bptr_gt_bptr_bptr (atstype_ptr bp,
                                atstype_ptr bq)
{
  return (bp > bq);
}

ats2_timsort_bptr_inline atstype_bool
ats2_timsort_bptr_gte_bptr_bptr (atstype_ptr bp,
                                 atstype_ptr bq)
{
  return (bp >= bq);
}

ats2_timsort_bptr_inline atstype_bool
ats2_timsort_bptr_eq_bptr_bptr (atstype_ptr bp,
                                atstype_ptr bq)
{
  return (bp == bq);
}

ats2_timsort_bptr_inline atstype_bool
ats2_timsort_bptr_neq_bptr_bptr (atstype_ptr bp,
                                 atstype_ptr bq)
{
  return (bp != bq);
}

ats2_timsort_bptr_inline atstype_int
ats2_timsort_bptr_compare_bptr_bptr (atstype_ptr bp,
                                     atstype_ptr bq)
{
  return ((bp < bq) ? (-1) : ((bp > bq) ? 1 : 0));
}

#endif /* TIMSORT__CATS__BPTR_CATS__HEADER_GUARD__ */

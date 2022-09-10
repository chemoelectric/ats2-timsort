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

#ifndef ATS2_TIMSORT_H__HEADER_GUARD__
#define ATS2_TIMSORT_H__HEADER_GUARD__

#include <stdlib.h>

typedef void ats2_timsort_c_timsort_t (void *, size_t, void *);
typedef const void *ats2_timsort_c_pointer;
typedef int ats2_timsort_c_bool;

ats2_timsort_c_timsort_t ats2_timsort_c_pointer_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_int_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_unsigned_int_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_signed_char_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_unsigned_char_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_short_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_unsigned_short_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_long_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_unsigned_long_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_long_long_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_unsigned_long_long_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_float_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_double_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_long_double_timsort;

static inline void
pointer_timsort (ats2_timsort_c_pointer *arr,
                 size_t n,
                 ats2_timsort_c_bool
                 (*less_than) (ats2_timsort_c_pointer,
                               ats2_timsort_c_pointer))
{
  ats2_timsort_c_pointer_timsort (arr, n, less_than);
}

static inline void
int_timsort (int *arr,
             size_t n,
             ats2_timsort_c_bool (*less_than) (int, int))
{
  ats2_timsort_c_int_timsort (arr, n, less_than);
}

static inline void
unsigned_int_timsort (unsigned int *arr,
                      size_t n,
                      ats2_timsort_c_bool (*less_than) (int, int))
{
  ats2_timsort_c_unsigned_int_timsort (arr, n, less_than);
}

static inline void
signed_char_timsort (signed char *arr,
                     size_t n,
                     ats2_timsort_c_bool
                     (*less_than) (signed char,
                                   signed char))
{
  ats2_timsort_c_signed_char_timsort (arr, n, less_than);
}

static inline void
unsigned_char_timsort (unsigned char *arr,
                       size_t n,
                       ats2_timsort_c_bool
                       (*less_than) (unsigned char,
                                     unsigned char))
{
  ats2_timsort_c_unsigned_char_timsort (arr, n, less_than);
}

static inline void
short_timsort (short *arr,
               size_t n,
               ats2_timsort_c_bool (*less_than) (short, short))
{
  ats2_timsort_c_short_timsort (arr, n, less_than);
}

static inline void
unsigned_short_timsort (unsigned short *arr,
                        size_t n,
                        ats2_timsort_c_bool
                        (*less_than) (unsigned short,
                                      unsigned short))
{
  ats2_timsort_c_unsigned_short_timsort (arr, n, less_than);
}

static inline void
long_timsort (long *arr,
              size_t n,
              ats2_timsort_c_bool (*less_than) (long, long))
{
  ats2_timsort_c_long_timsort (arr, n, less_than);
}

static inline void
unsigned_long_timsort (unsigned long *arr,
                       size_t n,
                       ats2_timsort_c_bool
                       (*less_than) (unsigned long,
                                     unsigned long))
{
  ats2_timsort_c_unsigned_long_timsort (arr, n, less_than);
}

static inline void
long_long_timsort (long long *arr,
                   size_t n,
                   ats2_timsort_c_bool
                   (*less_than) (long long,
                                 long long))
{
  ats2_timsort_c_long_long_timsort (arr, n, less_than);
}

static inline void
unsigned_long_long_timsort (unsigned long long *arr,
                            size_t n,
                            ats2_timsort_c_bool
                            (*less_than) (unsigned long long,
                                          unsigned long long))
{
  ats2_timsort_c_unsigned_long_long_timsort (arr, n, less_than);
}

static inline void
float_timsort (float *arr,
               size_t n,
               ats2_timsort_c_bool (*less_than) (float, float))
{
  ats2_timsort_c_float_timsort (arr, n, less_than);
}

static inline void
double_timsort (double *arr,
                size_t n,
                ats2_timsort_c_bool (*less_than) (double, double))
{
  ats2_timsort_c_double_timsort (arr, n, less_than);
}

static inline void
long_double_timsort (long double *arr,
                     size_t n,
                     ats2_timsort_c_bool
                     (*less_than) (long double,
                                   long double))
{
  ats2_timsort_c_long_double_timsort (arr, n, less_than);
}

#endif /* ATS2_TIMSORT_H__HEADER_GUARD__ */

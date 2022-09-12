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
#include <stdint.h>

typedef void ats2_timsort_c_timsort_t (void *, size_t, void *);
typedef void ats2_timsort_c_timsort_r_t (void *, size_t, void *,
                                         void *);
typedef const void *ats2_timsort_c_pointer;
typedef int ats2_timsort_c_bool;

/*------------------------------------------------------------------*/
/* Hooks for customizing the memory management.                     */

extern void (*ats2_timsort_c_minit_hook) (void);
extern void (*ats2_timsort_c_mfree_hook) (void *p);
extern void *(*ats2_timsort_c_malloc_hook) (size_t size);
extern void *(*ats2_timsort_c_calloc_hook) (size_t nmemb,
                                            size_t size);
extern void *(*ats2_timsort_c_realloc_hook) (void *p,
                                             size_t size);

/*------------------------------------------------------------------*/
/* Non-reentrant extern functions, without much typechecking.       */

ats2_timsort_c_timsort_t ats2_timsort_c_pointer_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_int_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_signed_char_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_short_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_long_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_long_long_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_unsigned_int_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_unsigned_char_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_unsigned_short_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_unsigned_long_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_unsigned_long_long_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_float_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_double_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_long_double_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_ssize_t_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_intptr_t_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_intmax_t_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_size_t_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_uintptr_t_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_uintmax_t_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_int8_t_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_int16_t_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_int32_t_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_int64_t_timsort;

ats2_timsort_c_timsort_t ats2_timsort_c_uint8_t_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_uint16_t_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_uint32_t_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_uint64_t_timsort;

#ifdef __SIZEOF_INT128__
ats2_timsort_c_timsort_t ats2_timsort_c_int128_t_timsort;
ats2_timsort_c_timsort_t ats2_timsort_c_uint128_t_timsort;
#endif

/*------------------------------------------------------------------*/
/* Reentrant extern functions, without much typechecking.           */

ats2_timsort_c_timsort_r_t ats2_timsort_c_pointer_timsort_r;

ats2_timsort_c_timsort_r_t ats2_timsort_c_float_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_double_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_long_double_timsort_r;

ats2_timsort_c_timsort_r_t ats2_timsort_c_int_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_signed_char_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_short_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_long_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_long_long_timsort_r;

ats2_timsort_c_timsort_r_t ats2_timsort_c_unsigned_int_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_unsigned_char_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_unsigned_short_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_unsigned_long_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_unsigned_long_long_timsort_r;

ats2_timsort_c_timsort_r_t ats2_timsort_c_ssize_t_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_intptr_t_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_intmax_t_timsort_r;

ats2_timsort_c_timsort_r_t ats2_timsort_c_size_t_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_uintptr_t_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_uintmax_t_timsort_r;

ats2_timsort_c_timsort_r_t ats2_timsort_c_int8_t_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_int16_t_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_int32_t_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_int64_t_timsort_r;

ats2_timsort_c_timsort_r_t ats2_timsort_c_uint8_t_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_uint16_t_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_uint32_t_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_uint64_t_timsort_r;

#ifdef __SIZEOF_INT128__
ats2_timsort_c_timsort_r_t ats2_timsort_c_int128_t_timsort_r;
ats2_timsort_c_timsort_r_t ats2_timsort_c_uint128_t_timsort_r;
#endif

/*------------------------------------------------------------------*/
/* Non-reentrant inline interfaces, with typechecking.              */

#define ATS2_TIMSORT_C_DEFINE_FUNCTION(F, T)            \
  static inline void                                    \
  F##_timsort (T *arr, size_t n,                        \
               ats2_timsort_c_bool (*less_than) (T, T)) \
  {                                                     \
    ats2_timsort_c_##F##_timsort (arr, n, less_than);   \
  }

ATS2_TIMSORT_C_DEFINE_FUNCTION (pointer, ats2_timsort_c_pointer)

ATS2_TIMSORT_C_DEFINE_FUNCTION (float, float)
ATS2_TIMSORT_C_DEFINE_FUNCTION (double, double)
ATS2_TIMSORT_C_DEFINE_FUNCTION (long_double, long double)

ATS2_TIMSORT_C_DEFINE_FUNCTION (int, int)
ATS2_TIMSORT_C_DEFINE_FUNCTION (signed_char, signed char)
ATS2_TIMSORT_C_DEFINE_FUNCTION (short, short)
ATS2_TIMSORT_C_DEFINE_FUNCTION (long, long)
ATS2_TIMSORT_C_DEFINE_FUNCTION (long_long, long long)

ATS2_TIMSORT_C_DEFINE_FUNCTION (unsigned_int, unsigned int)
ATS2_TIMSORT_C_DEFINE_FUNCTION (unsigned_char, unsigned char)
ATS2_TIMSORT_C_DEFINE_FUNCTION (unsigned_short, unsigned short)
ATS2_TIMSORT_C_DEFINE_FUNCTION (unsigned_long, unsigned long)
ATS2_TIMSORT_C_DEFINE_FUNCTION (unsigned_long_long, unsigned long long)

ATS2_TIMSORT_C_DEFINE_FUNCTION (ssize_t, ssize_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION (intptr_t, intptr_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION (intmax_t, intmax_t)

ATS2_TIMSORT_C_DEFINE_FUNCTION (size_t, size_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION (uintptr_t, uintptr_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION (uintmax_t, uintmax_t)

ATS2_TIMSORT_C_DEFINE_FUNCTION (int8_t, int8_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION (int16_t, int16_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION (int32_t, int32_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION (int64_t, int64_t)

ATS2_TIMSORT_C_DEFINE_FUNCTION (uint8_t, uint8_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION (uint16_t, uint16_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION (uint32_t, uint32_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION (uint64_t, uint64_t)

#ifdef __SIZEOF_INT128__
ATS2_TIMSORT_C_DEFINE_FUNCTION (int128_t, __int128_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION (uint128_t, __uint128_t)
#endif

/*------------------------------------------------------------------*/
/* Reentrant inline interfaces, with typechecking.                  */

#define ATS2_TIMSORT_C_DEFINE_FUNCTION_R(F, T)                      \
  static inline void                                                \
  F##_timsort_r (T *arr, size_t n,                                  \
                 ats2_timsort_c_bool (*less_than) (T, T, void *),   \
                 void *environment)                                 \
  {                                                                 \
    ats2_timsort_c_##F##_timsort_r (arr, n, less_than,              \
                                    environment);                   \
  }

ATS2_TIMSORT_C_DEFINE_FUNCTION_R (pointer, ats2_timsort_c_pointer)

ATS2_TIMSORT_C_DEFINE_FUNCTION_R (float, float)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (double, double)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (long_double, long double)

ATS2_TIMSORT_C_DEFINE_FUNCTION_R (int, int)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (signed_char, signed char)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (short, short)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (long, long)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (long_long, long long)

ATS2_TIMSORT_C_DEFINE_FUNCTION_R (unsigned_int, unsigned int)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (unsigned_char, unsigned char)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (unsigned_short, unsigned short)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (unsigned_long, unsigned long)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (unsigned_long_long, unsigned long long)

ATS2_TIMSORT_C_DEFINE_FUNCTION_R (ssize_t, ssize_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (intptr_t, intptr_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (intmax_t, intmax_t)

ATS2_TIMSORT_C_DEFINE_FUNCTION_R (size_t, size_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (uintptr_t, uintptr_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (uintmax_t, uintmax_t)

ATS2_TIMSORT_C_DEFINE_FUNCTION_R (int8_t, int8_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (int16_t, int16_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (int32_t, int32_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (int64_t, int64_t)

ATS2_TIMSORT_C_DEFINE_FUNCTION_R (uint8_t, uint8_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (uint16_t, uint16_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (uint32_t, uint32_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (uint64_t, uint64_t)

#ifdef __SIZEOF_INT128__
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (int128_t, __int128_t)
ATS2_TIMSORT_C_DEFINE_FUNCTION_R (uint128_t, __uint128_t)
#endif

/*------------------------------------------------------------------*/

#endif /* ATS2_TIMSORT_H__HEADER_GUARD__ */

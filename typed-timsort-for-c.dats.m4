(*
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
*)

include(`common-macros.m4')
divert(-1)

m4_define(`FUNCNAME',`TYPE`_timsort'')

dnl m4_define(`CTYPE',
dnl   `m4_if(TYPE,`pointer',`void *',
dnl          TYPE,`unsigned_int',`unsigned int',
dnl          TYPE,`signed_char',`signed char',
dnl          TYPE,`unsigned_char',`unsigned char',
dnl          TYPE,`unsigned_short',`unsigned short',
dnl          TYPE,`unsigned_long',`unsigned long',
dnl          TYPE,`long_long',`long long',
dnl          TYPE,`unsigned_long_long',`unsigned long long',
dnl          TYPE,`long_double',`long double',
dnl          TYPE)')

m4_define(`ATSTYPE',
  `m4_if(TYPE,`pointer',`ptr',
         TYPE,`unsigned_int',`uint',
         TYPE,`signed_char',`schar',
         TYPE,`unsigned_char',`uchar',
         TYPE,`short',`sint',
         TYPE,`unsigned_short',`usint',
         TYPE,`long',`lint',
         TYPE,`unsigned_long',`ulint',
         TYPE,`long_long',`llint',
         TYPE,`unsigned_long_long',`ullint',
         TYPE,`long_double',`ldouble',
         TYPE,`intptr_t',`intptr',
         TYPE,`uintptr_t',`uintptr',
         TYPE,`int8_t',`int8',
         TYPE,`uint8_t',`uint8',
         TYPE,`int16_t',`int16',
         TYPE,`uint16_t',`uint16',
         TYPE,`int32_t',`int32',
         TYPE,`uint32_t',`uint32',
         TYPE,`int64_t',`int64',
         TYPE,`uint64_t',`uint64',
         TYPE)')

dnl m4_define(`IS_BUILTIN_TYPE',
dnl   `m4_if(TYPE,`pointer',1,
dnl          TYPE,`int',1,
dnl          TYPE,`unsigned_int',1,
dnl          TYPE,`signed_char',1,
dnl          TYPE,`unsigned_char',1,
dnl          TYPE,`short',1,
dnl          TYPE,`unsigned_short',1,
dnl          TYPE,`long',1,
dnl          TYPE,`unsigned_long',1,
dnl          TYPE,`long_long',1,
dnl          TYPE,`unsigned_long_long',1,
dnl          TYPE,`float',1,
dnl          TYPE,`double',1,
dnl          TYPE,`long_double',1,
dnl          0)')

m4_define(`IS_SIGNED_TYPE',
  `m4_if(TYPE,`int',1,
         TYPE,`signed_char',1,
         TYPE,`short',1,
         TYPE,`long',1,
         TYPE,`long_long',1,
         TYPE,`ssize_t',1,
         TYPE,`intptr_t',1,
         TYPE,`int8_t',1,
         TYPE,`int16_t',1,
         TYPE,`int32_t',1,
         TYPE,`int64_t',1,
         0)')

dnl m4_define(`SIZEOF',
dnl   `m4_if(TYPE,`int',SIZEOF_INT,
dnl          TYPE,`unsigned_int',SIZEOF_UNSIGNED_INT,
dnl          TYPE,`signed_char',SIZEOF_SIGNED_CHAR,
dnl          TYPE,`unsigned_char',SIZEOF_UNSIGNED_CHAR,
dnl          TYPE,`short',SIZEOF_SHORT,
dnl          TYPE,`unsigned_short',SIZEOF_UNSIGNED_SHORT,
dnl          TYPE,`long',SIZEOF_LONG,
dnl          TYPE,`unsigned_long',SIZEOF_UNSIGNED_LONG,
dnl          TYPE,`long_long',SIZEOF_LONG_LONG,
dnl          TYPE,`unsigned_long_long',SIZEOF_UNSIGNED_LONG_LONG,
dnl          TYPE,`ssize_t',SIZEOF_SSIZE_T,
dnl          TYPE,`size_t',SIZEOF_SIZE_T,
dnl          TYPE,`intptr_t',SIZEOF_INTPTR_T
dnl          TYPE,`uintptr_t',SIZEOF_UINTPTR_T,
dnl          TYPE,`int8_t',SIZEOF_INT8_T,
dnl          TYPE,`uint8_t',SIZEOF_UINT8_T,
dnl          TYPE,`int16_t',SIZEOF_INT16_T,
dnl          TYPE,`uint16_t',SIZEOF_UINT16_T,
dnl          TYPE,`int32_t',SIZEOF_INT32_T,
dnl          TYPE,`uint32_t',SIZEOF_UINT32_T,
dnl          TYPE,`int64_t',SIZEOF_INT64_T,
dnl          TYPE,`uint64_t',SIZEOF_UINT64_T,
dnl          `type not handled')')

m4_define(`DEFAULT_DEFINITION',
`
extern fn
ats2_timsort_c_`'FUNCNAME
          {n         : int}
          {arrsz     : int | n <= arrsz}
          (arr       : &array (ATSTYPE, arrsz),
           n         : size_t n,
           less_than : (ATSTYPE, ATSTYPE) -<fun> int)
    : void = "ext#ats2_timsort_c_`'FUNCNAME"

implement
ats2_timsort_c_`'FUNCNAME (arr, n, less_than) =
  let
    implement
    array_timsort$lt<ATSTYPE> (x, y) =
      (x \less_than y) <> 0
  in
    array_timsort<ATSTYPE> (arr, n)
  end
')

m4_define(`INDIRECT_DEFINITION',
`
%{
void
ats2_timsort_c_`'FUNCNAME (void *arr, size_t n, void *less_than)
{
  ats2_timsort_c_`'$1`'_timsort (arr, n, less_than);
}
%}
')

m4_define(`SIGNED_DEFINITION',
  `m4_if($1,SIZEOF_INT,`INDIRECT_DEFINITION(int)',
         $1,SIZEOF_SIGNED_CHAR,`INDIRECT_DEFINITION(signed_char)',
         $1,SIZEOF_SHORT,`INDIRECT_DEFINITION(short)',
         $1,SIZEOF_LONG,`INDIRECT_DEFINITION(long)',
         $1,SIZEOF_LONG_LONG,`INDIRECT_DEFINITION(long_long)',
         `DEFAULT_DEFINITION')')

m4_define(`UNSIGNED_DEFINITION',
  `m4_if($1,SIZEOF_UNSIGNED_INT,`INDIRECT_DEFINITION(unsigned_int)',
         $1,SIZEOF_UNSIGNED_CHAR,`INDIRECT_DEFINITION(unsigned_char)',
         $1,SIZEOF_UNSIGNED_SHORT,`INDIRECT_DEFINITION(unsigned_short)',
         $1,SIZEOF_UNSIGNED_LONG,`INDIRECT_DEFINITION(unsigned_long)',
         $1,SIZEOF_UNSIGNED_LONG_LONG,`INDIRECT_DEFINITION(unsigned_long_long)',
         `DEFAULT_DEFINITION')')

divert

#define ATS_DYNLOADFLAG 0

#define ATS_PACKNAME "ats2-timsort-c"
#define ATS_EXTERN_PREFIX "ats2_timsort_c_"

#include "share/atspre_staload.hats"
#include "timsort/HATS/array-timsort.hats"

%{^
#include "ats2-timsort.h"
#include "timsort-for-c-memory.h"
%}

m4_if(TYPE,`short',
        `m4_if(SIZEOF_SHORT,SIZEOF_INT,`INDIRECT_DEFINITION(int)',
              `DEFAULT_DEFINITION')',
      TYPE,`unsigned_short',
        `m4_if(SIZEOF_UNSIGNED_SHORT,SIZEOF_UNSIGNED_INT,`INDIRECT_DEFINITION(unsigned_int)',
               `DEFAULT_DEFINITION')',

      TYPE,`long',
        `m4_if(SIZEOF_LONG,SIZEOF_INT,`INDIRECT_DEFINITION(int)',
               `DEFAULT_DEFINITION')',
      TYPE,`unsigned_long',
        `m4_if(SIZEOF_UNSIGNED_LONG,SIZEOF_UNSIGNED_INT,`INDIRECT_DEFINITION(unsigned_int)',
               `DEFAULT_DEFINITION')',

      TYPE,`long_long',
        `m4_if(SIZEOF_LONG_LONG,SIZEOF_INT,`INDIRECT_DEFINITION(int)',
               SIZEOF_LONG_LONG,SIZEOF_LONG,`INDIRECT_DEFINITION(long)',
               `DEFAULT_DEFINITION')',
      TYPE,`unsigned_long_long',
        `m4_if(SIZEOF_UNSIGNED_LONG_LONG,SIZEOF_UNSIGNED_INT,`INDIRECT_DEFINITION(unsigned_int)',
               SIZEOF_UNSIGNED_LONG_LONG,SIZEOF_UNSIGNED_LONG,`INDIRECT_DEFINITION(unsigned_long)',
               `DEFAULT_DEFINITION')',

      TYPE,`ssize_t',SIGNED_DEFINITION(SIZEOF_SSIZE_T),
      TYPE,`intptr_t',SIGNED_DEFINITION(SIZEOF_INTPTR_T),
      TYPE,`intmax_t',SIGNED_DEFINITION(SIZEOF_INTMAX_T),

      TYPE,`size_t',UNSIGNED_DEFINITION(SIZEOF_SIZE_T),
      TYPE,`uintptr_t',UNSIGNED_DEFINITION(SIZEOF_UINTPTR_T),
      TYPE,`uintmax_t',UNSIGNED_DEFINITION(SIZEOF_UINTMAX_T),

      TYPE,`int8_t',SIGNED_DEFINITION(SIZEOF_INT8_T),
      TYPE,`int16_t',SIGNED_DEFINITION(SIZEOF_INT16_T),
      TYPE,`int32_t',SIGNED_DEFINITION(SIZEOF_INT32_T),
      TYPE,`int64_t',SIGNED_DEFINITION(SIZEOF_INT64_T),

      TYPE,`uint8_t',UNSIGNED_DEFINITION(SIZEOF_UINT8_T),
      TYPE,`uint16_t',UNSIGNED_DEFINITION(SIZEOF_UINT16_T),
      TYPE,`uint32_t',UNSIGNED_DEFINITION(SIZEOF_UINT32_T),
      TYPE,`uint64_t',UNSIGNED_DEFINITION(SIZEOF_UINT64_T),

      `DEFAULT_DEFINITION')

dnl local variables:
dnl mode: ats
dnl end:

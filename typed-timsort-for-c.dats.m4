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

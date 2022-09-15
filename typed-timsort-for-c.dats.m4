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
m4_include(`timsort-macros.m4')

#define ATS_DYNLOADFLAG 0

#define ATS_PACKNAME "ats2-timsort-c"
#define ATS_EXTERN_PREFIX "ats2_timsort_c_"

#include "share/atspre_staload.hats"
#include "timsort/HATS/array-timsort.hats"

%{^

#include "ats2-timsort.h"
#include "timsort-for-c-memory.h"

#ifndef __STDC_WANT_IEC_60559_BFP_EXT__
#define __STDC_WANT_IEC_60559_BFP_EXT__ 1
#endif

#ifndef __STDC_WANT_IEC_60559_DFP_EXT__
#define __STDC_WANT_IEC_60559_DFP_EXT__ 1
#endif

#ifndef __STDC_WANT_IEC_60559_TYPES_EXT__
#define __STDC_WANT_IEC_60559_TYPES_EXT__ 1
#endif

#ifndef __STDC_WANT_IEC_60559_FUNCS_EXT__
#define __STDC_WANT_IEC_60559_FUNCS_EXT__ 1
#endif

#ifndef __STDC_WANT_IEC_60559_ATTRIBS_EXT__
#define __STDC_WANT_IEC_60559_ATTRIBS_EXT__ 1
#endif

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

      TYPE,`int128_t',SIGNED_DEFINITION(SIZEOF_INT128_T),
      TYPE,`uint128_t',UNSIGNED_DEFINITION(SIZEOF_UINT128_T),

      `DEFAULT_DEFINITION')

dnl local variables:
dnl mode: ats
dnl end:

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

#ifndef TIMSORT_FOR_C_MEMORY_H__HEADER_GUARD__
#define TIMSORT_FOR_C_MEMORY_H__HEADER_GUARD__

#include <stdlib.h>

#undef ATS_MEMALLOC_LIBC
#undef ATS_MEMALLOC_GCBDW
#undef ATS_MEMALLOC_USER

#undef ATS_MINIT
#undef ATS_MFREE
#undef ATS_MALLOC
#undef ATS_CALLOC
#undef ATS_REALLOC

#define ATS_MINIT ats2_timsort_c_minit
#define ATS_MFREE ats2_timsort_c_mfree
#define ATS_MALLOC ats2_timsort_c_malloc
#define ATS_CALLOC ats2_timsort_c_calloc
#define ATS_REALLOC ats2_timsort_c_realloc

extern void ats2_timsort_c_minit (void);
extern void ats2_timsort_c_mfree (atstype_ptr p);
extern atstype_ptr ats2_timsort_c_malloc (atstype_size size);
extern atstype_ptr ats2_timsort_c_calloc (atstype_size nmemb,
                                          atstype_size size);
extern atstype_ptr ats2_timsort_c_realloc (atstype_ptr p,
                                           atstype_size size);

#endif /* TIMSORT_FOR_C_MEMORY_H__HEADER_GUARD__ */

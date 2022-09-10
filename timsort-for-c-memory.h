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

#include <stdlib.h>

#undef ATS_MEMALLOC_LIBC
#undef ATS_MEMALLOC_GCBDW
#undef ATS_MEMALLOC_USER

#undef ATS_MINIT
#undef ATS_MFREE
#undef ATS_MALLOC
#undef ATS_CALLOC
#undef ATS_REALLOC

#define ATS_MINIT ats2_timsort_minit
#define ATS_MFREE ats2_timsort_mfree
#define ATS_MALLOC ats2_timsort_malloc
#define ATS_CALLOC ats2_timsort_calloc
#define ATS_REALLOC ats2_timsort_realloc

ATSinline() void
ats2_timsort_minit (void)
{
  return;
}

ATSinline() void
ats2_timsort_mfree (atstype_ptr p)
{
  free (p);
}

ATSinline() atstype_ptr
ats2_timsort_malloc (atstype_size size)
{
  atstype_ptr p = malloc (size);
  if (p == NULL)
    {
      fprintf (stderr, "ats2-timsort: malloc failed.\n");
      exit (1);
    }
  return p;
}

ATSinline() atstype_ptr
ats2_timsort_calloc (atstype_size nmemb, atstype_size size)
{
  atstype_ptr p = calloc (nmemb, size);
  if (p == NULL)
    {
      fprintf (stderr, "ats2-timsort: calloc failed.\n");
      exit (1);
    }
  return p;
}

ATSinline() atstype_ptr
ats2_timsort_realloc (atstype_ptr p, atstype_size size)
{
  atstype_ptr q = realloc (p, size);
  if (q == NULL)
    {
      fprintf (stderr, "ats2-timsort: realloc failed.\n");
      exit (1);
    }
  return q;
}

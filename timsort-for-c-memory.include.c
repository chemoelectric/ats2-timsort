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

#include "timsort-for-c-memory.h"
#include "ats2-timsort.h"

void (*ats2_timsort_c_minit_hook) (void) = NULL;
void (*ats2_timsort_c_mfree_hook) (void *p) = NULL;
void *(*ats2_timsort_c_malloc_hook) (size_t size) = NULL;
void *(*ats2_timsort_c_calloc_hook) (size_t nmemb,
                                     size_t size) = NULL;
void *(*ats2_timsort_c_realloc_hook) (void *p,
                                      size_t size) = NULL;

void
ats2_timsort_c_minit (void)
{
  if (ats2_timsort_c_minit_hook != NULL)
    ats2_timsort_c_minit_hook ();
}

void
ats2_timsort_c_mfree (atstype_ptr p)
{
  if (ats2_timsort_c_mfree_hook != NULL)
    ats2_timsort_c_mfree_hook (p);
  else
    free (p);
}

atstype_ptr
ats2_timsort_c_malloc (atstype_size size)
{
  atstype_ptr p;

  if (ats2_timsort_c_malloc_hook != NULL)
    p = ats2_timsort_c_malloc_hook (size);
  else
    {
      p = malloc (size);
      if (p == NULL)
        {
          fprintf (stderr, "ats2-timsort: malloc failed.\n");
          exit (1);
        }
    }
  return p;
}

atstype_ptr
ats2_timsort_c_calloc (atstype_size nmemb, atstype_size size)
{
  atstype_ptr p;

  if (ats2_timsort_c_calloc_hook != NULL)
    p = ats2_timsort_c_calloc_hook (nmemb, size);
  else
    {
      p = calloc (nmemb, size);
      if (p == NULL)
        {
          fprintf (stderr, "ats2-timsort: calloc failed.\n");
          exit (1);
        }
    }
  return p;
}

atstype_ptr
ats2_timsort_c_realloc (atstype_ptr p, atstype_size size)
{
  atstype_ptr q;

  if (ats2_timsort_c_realloc_hook != NULL)
    q = ats2_timsort_c_realloc_hook (p, size);
  else
    {
      q = realloc (p, size);
      if (q == NULL)
        {
          fprintf (stderr, "ats2-timsort: realloc failed.\n");
          exit (1);
        }
    }
  return q;
}

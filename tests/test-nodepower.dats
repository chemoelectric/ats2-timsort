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

(* Unit testing of nodepower implementations. *)

%{^

#include <limits.h>
#include <timsort/CATS/timsort.cats>

#define CHECK(expr)                             \
  if (expr)                                     \
    {}                                          \
  else                                          \
    check_failed (__FILE__, __LINE__)

static void
check_failed (const char *file, unsigned int line)
{
  fprintf (stderr, "CHECK failed at %s:%u\n", file, line);
  exit (1);
}

atstype_int
clz (atstype_size bits)
{
  return ats2_timsort_g0uint_clz_size (bits);
}

atstype_int
clz_fallback (atstype_size bits)
{
  return ats2_timsort_g0uint_clz_size_fallback (bits);
}

atstype_int
nodepower_fallback (atstype_size n, atstype_size i,
                    atstype_size n1, atstype_size n2)
{
  return ats2_timsort_nodepower_fallback (n, i, n1, n2);
}

void
test_clz (void)
{
  const int bitsz = CHAR_BIT * sizeof (atstype_size);
  const atstype_size one = 1;
  const atstype_size all_ones = ~(atstype_size) 0;

  CHECK (clz (0) == bitsz);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz (one << i) == bitsz - 1 - i);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz (all_ones >> i) == i);
}

void
test_clz_fallback (void)
{
  const int bitsz = CHAR_BIT * sizeof (atstype_size);
  const atstype_size one = 1;
  const atstype_size all_ones = ~(atstype_size) 0;

  CHECK (clz_fallback (0) == bitsz);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz_fallback (one << i) == bitsz - 1 - i);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz_fallback (all_ones >> i) == i);
}

%}

implement
main0 () =
  begin
    $extfcall (void, "test_clz");
    $extfcall (void, "test_clz_fallback");
  end

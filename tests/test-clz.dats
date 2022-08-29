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

(* Unit testing of count-leading-zeros implementations. *)

#include "share/atspre_staload.hats"

staload "timsort/SATS/COMMON/timsort-common.sats"
staload _ = "timsort/DATS/COMMON/timsort-common.dats"

%{^

#include <limits.h>
#include <timsort/CATS/timsort.cats>

#define SKIP_TEST -12345

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
clz_ullint (atstype_ullint bits)
{
  return ats2_timsort_g0uint_clz_ullint (bits);
}

atstype_int
clz_ullint_fallback (atstype_ullint bits)
{
  return ats2_timsort_g0uint_clz_ullint_fallback (bits);
}

atstype_int
clz_size (atstype_size bits)
{
  return ats2_timsort_g0uint_clz_size (bits);
}

void
test_clz_ullint (void)
{
  const int bitsz = CHAR_BIT * sizeof (atstype_ullint);
  const atstype_ullint one = 1;
  const atstype_ullint all_ones = ~(atstype_ullint) 0;

  CHECK (clz_ullint (0) == bitsz);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz_ullint (one << i) == bitsz - 1 - i);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz_ullint (all_ones >> i) == i);
}

void
test_clz_ullint_fallback (void)
{
  const int bitsz = CHAR_BIT * sizeof (atstype_ullint);
  const atstype_ullint one = 1;
  const atstype_ullint all_ones = ~(atstype_ullint) 0;

  CHECK (clz_ullint_fallback (0) == bitsz);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz_ullint_fallback (one << i) == bitsz - 1 - i);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz_ullint_fallback (all_ones >> i) == i);
}

void
test_clz_size (void)
{
  const int bitsz = CHAR_BIT * sizeof (atstype_size);
  const atstype_size one = 1;
  const atstype_size all_ones = ~(atstype_size) 0;

  CHECK (clz_size (0) == bitsz);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz_size (one << i) == bitsz - 1 - i);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz_size (all_ones >> i) == i);
}

%}

val char_bit = $extval (Size_t, "((atstype_size) CHAR_BIT)")

fn {tk : tkind}
test2_clz () : void =
  let
    val zero : g0uint tk = g1i2u 0
    val one : g0uint tk = g1i2u 1
    val all_ones : g0uint tk = lnot zero

    val bitsz = sz2i (char_bit * sizeof<g1uint tk>)
    prval [bitsz : int] EQINT () = eqint_make_gint bitsz

    var i : [i : nat | i <= bitsz] int i
  in
    assertloc (clz zero = bitsz);
    for (i := 0; i <> bitsz; i := succ i)
      assertloc (clz (one << i) = pred bitsz - i);
    for (i := 0; i <> bitsz; i := succ i)
      assertloc (clz (all_ones >> i) = i);
  end

implement
main0 () =
  begin
    $extfcall (void, "test_clz_ullint");
    $extfcall (void, "test_clz_ullint_fallback");
    $extfcall (void, "test_clz_size");
    test2_clz<ullintknd> ();
    test2_clz<sizeknd> ()
  end

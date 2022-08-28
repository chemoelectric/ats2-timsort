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
clz (atstype_ullint bits)
{
  return ats2_timsort_g0uint_clz_ullint (bits);
}

atstype_int
clz_fallback (atstype_ullint bits)
{
  return ats2_timsort_g0uint_clz_ullint_fallback (bits);
}

atstype_int
nodepower (atstype_size n, atstype_size i,
           atstype_size n1, atstype_size n2)
{
  return ats2_timsort_nodepower (n, i, n1, n2);
}

atstype_int
nodepower_32bit (atstype_size n, atstype_size i,
                 atstype_size n1, atstype_size n2)
{
  atstype_int result;
  if (n <= 0xFFFFFFFF
      && sizeof (atstype_size) <= sizeof (atstype_ullint))
    ATS2_TIMSORT_NODEPOWER_PREFERRED (uint64_t, uint32_t);
  else
    result = SKIP_TEST;
  return result;
}

#ifdef __SIZEOF_INT128__
atstype_int
nodepower_64bit (atstype_size n, atstype_size i,
                 atstype_size n1, atstype_size n2)
{
  atstype_int result;
  if (sizeof (atstype_size) <= sizeof (atstype_uint64)
      && sizeof (atstype_size) <= sizeof (atstype_ullint))
    ATS2_TIMSORT_NODEPOWER_PREFERRED (__uint128_t, uint64_t);
  else
    result = SKIP_TEST;
  return result;
}
#else
atstype_int
nodepower_64bit (atstype_size n, atstype_size i,
                 atstype_size n1, atstype_size n2)
{
  return SKIP_TEST;
}
#endif

atstype_int
nodepower_fallback (atstype_size n, atstype_size i,
                    atstype_size n1, atstype_size n2)
{
  return ats2_timsort_nodepower_fallback (n, i, n1, n2);
}

void
test_clz (void)
{
  const int bitsz = CHAR_BIT * sizeof (atstype_ullint);
  const atstype_ullint one = 1;
  const atstype_ullint all_ones = ~(atstype_ullint) 0;

  CHECK (clz (0) == bitsz);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz (one << i) == bitsz - 1 - i);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz (all_ones >> i) == i);
}

void
test_clz_fallback (void)
{
  const int bitsz = CHAR_BIT * sizeof (atstype_ullint);
  const atstype_ullint one = 1;
  const atstype_ullint all_ones = ~(atstype_ullint) 0;

  CHECK (clz_fallback (0) == bitsz);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz_fallback (one << i) == bitsz - 1 - i);
  for (int i = 0; i != bitsz; i += 1)
    CHECK (clz_fallback (all_ones >> i) == i);
}

void
test_nodepower (atstype_int ( *func ) (atstype_size n,
                                       atstype_size i,
                                       atstype_size n1,
                                       atstype_size n2),
                atstype_string func_name,
                atstype_size n, atstype_size i,
                atstype_size n1, atstype_size n2,
                atstype_int expected)
{
  atstype_int got = func (n, i, n1, n2);
  if (got != SKIP_TEST)
    {
      if (got == expected)
        printf ("%s (%zu, %zu, %zu, %zu) == %d\n",
                func_name, n, i, n1, n2, got);
      else
        printf (("%s (%zu, %zu, %zu, %zu) == "
                 "{expected: %d; got: %d}\n"),
                func_name, n, i, n1, n2, expected, got);
      CHECK (got == expected);
    }
}

%}

typedef nodepower_test_set =
  @(size_t, size_t, size_t, size_t, int)

val nodepower = $extval (ptr, "nodepower")
val nodepower_32bit = $extval (ptr, "nodepower_32bit")
val nodepower_64bit = $extval (ptr, "nodepower_64bit")
val nodepower_fallback = $extval (ptr, "nodepower_fallback")

fn
test_nodepower () : void =
  let
    val test_sets =
      $list{nodepower_test_set}
        (@(i2sz 100, i2sz 0, i2sz 10, i2sz 90, 1))

    fun
    loop {len : nat}
         .<len>.
         (func      : ptr,
          func_name : string,
          p         : list (nodepower_test_set, len))
        : void =
      case+ p of
      | list_nil () => ()
      | list_cons (head, tail) =>
        let
          val @(n, i, n1, n2, expected) = head
        in
          $extfcall (void, "test_nodepower", func, func_name,
                     n, i, n1, n2, expected);
          loop (func, func_name, tail)
        end
  in
    loop (nodepower, "nodepower", test_sets);
    loop (nodepower_32bit, "nodepower_32bit", test_sets);
    loop (nodepower_64bit, "nodepower_64bit", test_sets);
    loop (nodepower_fallback, "nodepower_fallback", test_sets)
  end

implement
main0 () =
  begin
    $extfcall (void, "test_clz");
    $extfcall (void, "test_clz_fallback");
    test_nodepower ()
  end

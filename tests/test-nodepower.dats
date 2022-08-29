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
test_nodepower (atstype_int ( *func ) (atstype_size n,
                                       atstype_size i,
                                       atstype_size n1,
                                       atstype_size n2),
                atstype_string func_name,
                atstype_ullint n, atstype_ullint i,
                atstype_ullint n1, atstype_ullint n2,
                atstype_int expected)
{
  if (n <= ~(atstype_size) 0)
    {
    atstype_int got = func ((atstype_size) n, (atstype_size) i,
                            (atstype_size) n1, (atstype_size) n2);
    if (got != SKIP_TEST)
      {
        if (got == expected)
          printf ("%s (%llu, %llu, %llu, %llu) == %d\n",
                  func_name, n, i, n1, n2, got);
        else
          printf (("%s (%llu, %llu, %llu, %llu) == "
                   "{expected: %d; got: %d}\n"),
                  func_name, n, i, n1, n2, expected, got);
        CHECK (got == expected);
      }
  }
}

%}

typedef nodepower_test_set =
  @(ullint, ullint, ullint, ullint, int)

val nodepower = $extval (ptr, "nodepower")
val nodepower_32bit = $extval (ptr, "nodepower_32bit")
val nodepower_64bit = $extval (ptr, "nodepower_64bit")
val nodepower_fallback = $extval (ptr, "nodepower_fallback")

fn
test_nodepower () : void =
  let
    val test_sets =
      (* FIXME: Come up with a fuller and better set of tests
                cases. *)
      $list{nodepower_test_set}
        (@(100ULL, 0ULL, 10ULL, 90ULL, 1),
         @(0xFFFFFFFFULL, 1000ULL, 0xA0000000ULL, 0x0B000000ULL, 1),
         @(0xFFFFFFFFULL, 1000ULL, 10ULL, 0x0B000000ULL, 6),
         @(0xFFFFFFFFULL, 1000ULL, 1000ULL, 500ULL, 21),
         @(0x100000000ULL, 1000ULL, 0xA0000000ULL, 0x0B000000ULL, 1),
         @(0x100000000ULL, 1000ULL, 10ULL, 0x0B000000ULL, 6),
         @(0xFFFFFFFFFFFFFFFFULL, 1000ULL, 0xA000000000000000ULL,
           0x0B00000000000000ULL, 1),
         @(0xFFFFFFFFFFFFFFFFULL, 1000ULL, 10ULL,
           0x0B00000000000000ULL, 6),
         @(0xFFFFFFFFFFFFFFFFULL, 1000ULL, 1000ULL, 500ULL, 53))

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
  test_nodepower ()

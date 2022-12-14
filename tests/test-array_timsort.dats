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

#include "share/atspre_staload.hats"
staload UN = "prelude/SATS/unsafe.sats"

#include "timsort/HATS/array-timsort.hats"

#define NIL list_nil ()
#define ::  list_cons

(*------------------------------------------------------------------*)
(* A simple linear congruential generator.                          *)

%{^

static inline atstype_uint64
g1uint_mod_uint64 (atstype_uint64 x, atstype_uint64 y)
{
  return (x % y);
}

#if defined __GNUC__
#define BSWAP64 __builtin_bswap64
#else
#define BSWAP64(x)                                  \
  ((((x) & UINT64_C (0x00000000000000FF)) << 56) |  \
   (((x) & UINT64_C (0x000000000000FF00)) << 40) |  \
   (((x) & UINT64_C (0x0000000000FF0000)) << 24) |  \
   (((x) & UINT64_C (0x00000000FF000000)) << 8) |   \
   (((x) & UINT64_C (0x000000FF00000000)) >> 8) |   \
   (((x) & UINT64_C (0x0000FF0000000000)) >> 24) |  \
   (((x) & UINT64_C (0x00FF000000000000)) >> 40) |  \
   (((x) & UINT64_C (0xFF00000000000000)) >> 56))
#endif

/* The multiplier LCG_A comes from Steele, Guy; Vigna, Sebastiano (28
   September 2021). "Computationally easy, spectrally good multipliers
   for congruential pseudorandom number generators".
   arXiv:2001.05304v3 [cs.DS] */
#define LCG_A (UINT64_C (0xf1357aea2e62a9c5))

/* LCG_C must be odd. (The value 1 may get optimized to an increment
   instruction.) */
#define LCG_C (UINT64_C (1))

static uint64_t seed;

static inline atstype_uint64
random_uint64 (void)
{
  uint64_t old_seed = seed;

  /* The following operation is modulo 2**64, by virtue of standard C
     behavior for uint64_t. */
  seed = (LCG_A * old_seed) + LCG_C;

  /* Reverse the bytes, because least significant bits of LCG output
     tend to be bad. Indeed, the very least significant bit literally
     switches back and forth between 0 and 1. */
  return BSWAP64 (old_seed);
}

%}

extern fn
g1uint_mod_uint64 :
  {x, y : int}
  (uint64 x, uint64 y) -<> uint64 (x mod y) = "mac#g1uint_mod_uint64"

implement
g1uint_mod<uint64_kind> (x, y) =
  g1uint_mod_uint64 (x, y)

extern fn
random_uint64 () :<!wrt> uint64 = "mac#random_uint64"

fn {tk : tkind}
g1uint_randint
          {n : pos}
          (n : g1uint (tk, n))
    :<> [i : nat | i <= n - 1] g1uint (tk, i) =
  let
    val u64_n = $UN.cast{uint64 n} n
    val u64_rand : [i : nat] uint64 i =
      g1ofg0 ($effmask_wrt random_uint64 ())
    val u64_result = g1uint_mod (u64_rand, u64_n)
  in
    $UN.cast u64_result
  end

overload randint with g1uint_randint

(*------------------------------------------------------------------*)

typedef entry_t =
  @{
    key = int,
    value = int
  }

implement
list_equal$eqfn<entry_t> (x, y) =
  ((x.key) = (y.key)) * ((x.value) = (y.value))

implement
list_vt_mergesort$cmp<entry_t> (x, y) =
  if (x.key) < (y.key) then
    ~1
  else if (x.key) > (y.key) then
    1
  else
    0

implement
array_timsort$lt<entry_t> (x, y) =
  (x.key) < (y.key)

fn
fill_array_randomly
          {p_arr  : addr}
          {n      : int}
          (pf_arr : !array_v (entry_t, p_arr, n) |
           p_arr  : ptr p_arr,
           n      : size_t n)
    :<!wrt> void =
  let
    prval () = lemma_array_v_param pf_arr

    macdef arr = !p_arr

    fun
    loop {i : nat | i <= n}
         .<n - i>.
         (pf_arr : !array_v (entry_t, p_arr, n) |
          i      : size_t i)
        :<!wrt> void =
      if i <> n then
        let
          val entry =
            @{
              key = g1u2i (randint<uintknd> 1000U),
              value = succ (sz2i i)
            }
        in
          arr[i] := entry;
          loop (pf_arr | succ i)
        end
  in
    loop (pf_arr | i2sz 0)
  end

fun
display {n : nat}
        (p : list (entry_t, n))
    : void =
  case+ p of
  | NIL => ()
  | head :: tail =>
    begin
      println! (head.key, " -> ", head.value);
      display tail
    end

fn
test_array_of_size
          {n : nat}
          (n : size_t n)
    : void =
  let
    val @(pf_arr, pfgc_arr | p_arr) = array_ptr_alloc<entry_t> n
    val () = array_initize_elt (!p_arr, n, @{key = 0, value = 0})
    val () = fill_array_randomly (pf_arr | p_arr, n)

    val expected =
      list_vt2t (list_vt_mergesort<entry_t> (array2list (!p_arr, n)))

    val () = array_timsort<entry_t> (!p_arr, n)
    val gotten = list_vt2t (array2list (!p_arr, n))
    //val () = display gotten

    val () = assertloc (gotten = expected)

    val () = array_ptr_free (pf_arr, pfgc_arr | p_arr)
  in
  end

implement
main () =
  begin
    test_array_of_size (i2sz 0);
    test_array_of_size (i2sz 1);
    test_array_of_size (i2sz 2);
    test_array_of_size (i2sz 3);
    test_array_of_size (i2sz 4);
    test_array_of_size (i2sz 5);
    test_array_of_size (i2sz 6);
    test_array_of_size (i2sz 7);
    test_array_of_size (i2sz 8);
    test_array_of_size (i2sz 9);
    test_array_of_size (i2sz 10);
    test_array_of_size (i2sz 100);
    test_array_of_size (i2sz 1000);
    test_array_of_size (i2sz 10000);
    test_array_of_size (i2sz 100000);
    test_array_of_size (i2sz 1000000);
    0
  end

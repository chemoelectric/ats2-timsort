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

#define ATS_DYNLOADFLAG 0

#define ATS_PACKNAME "ats2-timsort"
#define ATS_EXTERN_PREFIX "ats2_timsort_"

#include "share/atspre_staload.hats"
staload UN = "prelude/SATS/unsafe.sats"

staload "timsort/SATS/COMMON/timsort-common.sats"

primplement
lemma_mul_isfun {m1, n1} {m2, n2} () =
  let
    prval pf1 = mul_make {m1, n1} ()
    prval pf2 = mul_make {m2, n2} ()
    prval () = mul_isfun {m1, n1} {m1 * n1, m2 * n2} (pf1, pf2)
  in
  end

primplement
lemma_mul_commutes {m, n} () =
  let
    prval pf1 = mul_make {m, n} ()
    prval pf2 = mul_commute pf1
    prval () = mul_elim pf2
  in
  end

primplement
array_v_takeout2 {a} {p} {n} {i, j} pf_arr =
  sif i < j then
    let
      prval @(pf1, pf1a) = array_v_split {a} {p} {n} {i} pf_arr
      prval @(pf2, pf3) =
        array_v_split {a} {p + (i * sizeof a)} {n - i} {j - i} pf1a
      prval @(pf_i, pf2a) =
        array_v_uncons {a} {p + (i * sizeof a)} {j - i} pf2
      prval @(pf_j, pf3a) =
        array_v_uncons {a} {p + (j * sizeof a)} {n - j} pf3
    in
      @(pf_i, pf_j,
        lam (pf_i, pf_j) =<lin,prf>
          let
            prval pf3 =
              array_v_cons
                {a} {p + (j * sizeof a)} {n - j - 1} (pf_j, pf3a)
            prval pf2 =
              array_v_cons
                {a} {p + (i * sizeof a)} {j - i - 1} (pf_i, pf2a)
            prval pf1a =
              array_v_unsplit {a} {p + (i * sizeof a)} {j - i, n - j}
                              (pf2, pf3)
            prval pf_arr =
              array_v_unsplit {a} {p} {i, n - i} (pf1, pf1a)
          in
            pf_arr
          end)
    end
  else
    let
      prval @(pf_j, pf_i, fpf_ji) =
        array_v_takeout2 {a} {p} {n} {j, i} pf_arr
    in
      @(pf_i, pf_j,
        lam (pf_i, pf_j) =<lin,prf> fpf_ji (pf_j, pf_i))
    end

(*------------------------------------------------------------------*)

implement g1uint_double<sizeknd> n =
  g1uint_double_size n

implement g0uint_ceildiv<sizeknd> (m, n) =
  g0uint_ceildiv_size (m, n)
implement g1uint_ceildiv<sizeknd> (m, n) =
  g1uint_ceildiv_size (m, n)

implement g0uint_is_even<sizeknd> n =
  g0uint_is_even_size n
implement g1uint_is_even<sizeknd> n =
  g1uint_is_even_size n

implement g0uint_is_odd<sizeknd> n =
  g0uint_is_odd_size n
implement g1uint_is_odd<sizeknd> n =
  g1uint_is_odd_size n

implement g0uint_clz<ullintknd> n =
  g0uint_clz_ullint n
implement g1uint_clz<ullintknd> n =
  g1uint_clz_ullint n

implement g0uint_clz<sizeknd> n =
  g0uint_clz_size n
implement g1uint_clz<sizeknd> n =
  g1uint_clz_size n

(*------------------------------------------------------------------*)

implement {}
stk_vt_make (pf | p, stk_max) =
  @{
    pf = pf |
    p = p,
    depth = 0,
    stk_max = stk_max
  }

implement {}
stk_vt_stk_max stk =
  stk.stk_max

implement {}
stk_vt_depth stk =
  stk.depth

implement {}
stk_vt_push (index, size, power, stk) =
  let
    macdef storage = !(stk.p)
  in
    stk.depth := succ (stk.depth);
    storage[stk.stk_max - stk.depth] :=
      @{
        index = index,
        size = size,
        power = power
      }
  end

implement {}
stk_vt_peek (stk, entry_num) =
  let
    macdef storage = !(stk.p)
  in
    storage[stk.stk_max - (stk.depth - entry_num)]
  end

implement {}
stk_vt_set_power (power, stk, entry_num) =
  let
    macdef storage = !(stk.p)
    val @{
          index = index,
          size = size,
          power = _
        } = storage[stk.stk_max - (stk.depth - entry_num)]
  in
    storage[stk.stk_max - (stk.depth - entry_num)] :=
      @{
        index = index,
        size = size,
        power = power
      }
  end

implement {}
stk_vt_drop stk =
  stk.depth := pred (stk.depth)

(*------------------------------------------------------------------*)

implement {}
minimum_run_length {n} n =
  if n < i2sz 64 then
    n                         (* The array is very small. *)
  else
    (* Divide n into a number of minimum-length runs that either is a
       power of two or is close to but less than a power of two.

       The routine isolates and shifts the six most significant bits
       of n. If any of the bits less significant than those was set,
       then one is added to the result. *)
    let
      prval () = prop_verify {0x3F < n} () (* Six one-digits. *)

      val bitsz =
        $extval (Size_t, "(CHAR_BIT * sizeof (atstype_size))")

      val leading0 = i2sz (clz n)
      val () = $effmask_exn assertloc (leading0 + i2sz 6 <= bitsz)
      val shift = sz2i (bitsz - leading0 - i2sz 6)
      val result = g1ofg0 (n >> shift)
      val () = $effmask_exn
        assertloc ((i2sz 32 <= result) * (result < i2sz 64))
    in
      if (result << shift) <> n then
        succ result
      else
        result
    end

#if 0 #then

(* Another possible implementation of minimum_run_length. *)
implement {}
minimum_run_length n =
  if n < i2sz 64 then
    n                         (* The array is very small. *)
  else
    (* Divide n into a number of minimum-length runs that either is a
       power of two or is close to but less than a power of two.

       The routine isolates and shifts the six most significant bits
       of n. If any of the bits less significant than those was set,
       then one is added to the result. *)
    let
      fun
      loop1 {q : int | 32 <= q}
            .<q>.
            (q : size_t q)
          :<> [minrun : int | 32 <= minrun; minrun <= 64]
              size_t minrun =
        if q < i2sz 64 then
          succ q
        else
          loop1 (half q)

      fun
      loop0 {q : int | 32 <= q}
            .<q>.
            (q : size_t q)
          :<> [minrun : int | 32 <= minrun; minrun <= 64]
              size_t minrun =
        if q < i2sz 64 then
          q
        else if is_even q then
          loop0 (half q)
        else
          loop1 (half q)
    in
      loop0 n
    end

#endif
      
(*------------------------------------------------------------------*)

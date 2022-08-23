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

staload "timsort/SATS/array-timsort.sats"
staload "timsort/SATS/COMMON/timsort-common.sats"
staload _ = "timsort/DATS/COMMON/timsort-common.dats"
staload "timsort/SATS/bptr.sats"
staload _ = "timsort/DATS/bptr.dats"

(*------------------------------------------------------------------*)

implement {a}
array_timsort$lt (x, y) =
  array_timsort$cmp<a> (x, y) < 0

implement {a}
array_timsort$cmp (x, y) =
  (* This default is the same as for array_quicksort$cmp in the
     prelude. *)
  gcompare_ref_ref<a> (x, y)

fn {a : vt@ype}
elem_lt_ptr1_ptr1
          {p, q : addr}
          (pf_p : !a @ p,
           pf_q : !a @ q |
           p    : ptr p,
           q    : ptr q)
    :<> bool =
  array_timsort$lt<a> (!p, !q)

fn {a : vt@ype}
elem_lt_bptr_bptr
          {p      : addr}
          {i, j   : int}
          (pf_i   : !a @ (p + (i * sizeof a)),
           pf_j   : !a @ (p + (j * sizeof a)) |
           bp_i   : bptr (a, p, i),
           bp_j   : bptr (a, p, j))
    :<> bool =
  elem_lt_ptr1_ptr1<a> (pf_i, pf_j | bptr2ptr bp_i, bptr2ptr bp_j)

fn {a : vt@ype}
elem_lt_array_bptr_bptr
          {p_arr  : addr}
          {n      : int}
          {i, j   : nat | i <= n - 1; j <= n - 1; i != j}
          (pf_arr : !array_v (a, p_arr, n) |
           bp_i   : bptr (a, p_arr, i),
           bp_j   : bptr (a, p_arr, j))
    :<> bool =
  let
    prval @(pf_i, pf_j, fpf) =
      array_v_takeout2 {a} {p_arr} {n} {i, j} pf_arr
    val is_lt =
      elem_lt_bptr_bptr<a> (pf_i, pf_j | bp_i, bp_j)
    prval () = pf_arr := fpf (pf_i, pf_j)
  in
    is_lt
  end

overload elem_lt with elem_lt_ptr1_ptr1
overload elem_lt with elem_lt_bptr_bptr
overload elem_lt with elem_lt_array_bptr_bptr

(*------------------------------------------------------------------*)

(* Compute a minimum run length. Runs shorter than this will be
   extended via an insertion sort. *)
extern fn {}
minimum_run_length :
  {n : int}
  size_t n -<>
    [minrun : int | min (n, 32) <= minrun; minrun <= 64]
    size_t minrun

(* A stable insertion sort that assumes the first runlen elements
   already are sorted. *)
extern fn {a : vt@ype}
insertion_sort_given_initial_sorted_run :
  {p_arr  : addr}
  {n      : int}
  {runlen : pos | runlen <= n}
  (!array_v (a, p_arr, n) |
   ptr p_arr,
   size_t runlen,
   size_t n) -< !wrt >
    void

(*------------------------------------------------------------------*)

implement {}
minimum_run_length n =
  if n < i2sz 64 then
    n       (* The array to be sorted is small. Use insertion sort. *)
  else
    (* The algorithm here is similar to that used in Python’s
       listsort, and tries to divide up n into a number of runs that
       is either a power of two or is close to but less than a power
       of two. *)
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

(*------------------------------------------------------------------*)

fn {a : vt@ype}
insertion_position
          {p_arr  : addr}
          {n      : int}
          {i      : pos | i < n}
          (pf_arr : !array_v (a, p_arr, n) |
           bp_arr : bptr_anchor (a, p_arr),
           bp_i   : bptr (a, p_arr, i))
    :<> [j : nat | j <= i]
        bptr (a, p_arr, j) =
  (*
    A binary search.

    References:

      * H. Bottenbruch, "Structure and use of ALGOL 60", Journal of
        the ACM, Volume 9, Issue 2, April 1962, pp.161-221.
        https://doi.org/10.1145/321119.321120

        The general algorithm is described on pages 214 and 215.

      * https://en.wikipedia.org/w/index.php?title=Binary_search_algorithm&oldid=1062988272#Alternative_procedure
  *)
  let
    fun
    loop {j, k : int | 0 <= j; j <= k; k < i}
         .<k - j>.
         (pf_arr : !array_v (a, p_arr, n) |
          bp_j   : bptr (a, p_arr, j),
          bp_k   : bptr (a, p_arr, k))
        :<> [j1 : nat | j1 <= i]
            bptr (a, p_arr, j1) =
      if bp_j <> bp_k then
        let
          (* Find the point that is halfway between bp_j and bp_k,
             rounding towards bp_k. *)
          stadef h = k - ((k - j) / 2)
          val bp_h : bptr (a, p_arr, h) =
            bptr_sub<a>
              (bp_k, half (bptr_diff_unsigned<a> (bp_k, bp_j)))
        in
          if elem_lt<a> (pf_arr | bp_i, bp_h) then
            loop (pf_arr | bp_j, bptr_pred<a> bp_h)
          else
            loop (pf_arr | bp_h, bp_k)
        end
      else if bp_j <> bp_arr then
        bptr_succ<a> bp_j
      else if elem_lt<a> (pf_arr | bp_i, bp_arr) then
        bp_arr
      else
        bptr_succ<a> bp_arr
  in
    loop (pf_arr | bp_arr, bptr_pred<a> bp_i)
  end

implement {a}
insertion_sort_given_initial_sorted_run {p_arr} {n}
                                        (pf_arr | p_arr, runlen, n) =
  let
    val bp_arr = ptr2bptr_anchor p_arr

    val bp_i = bptr_add<a> (bp_arr, runlen)
    and bp_n = bptr_add<a> (bp_arr, n)

    fun
    loop {i : pos | i <= n}
         .<n - i>.
         (pf_arr : !array_v (a, p_arr, n) >> _ |
          bp_i   : bptr (a, p_arr, i))
        :<!wrt> void =
      if bp_i <> bp_n then
        let
          val bp_j = insertion_position<a> (pf_arr | bp_arr, bp_i)
        in
          subcirculate_right<a> (pf_arr | bp_j, bp_i);
          loop (pf_arr | bptr_succ<a> bp_i)
        end
  in
    loop (pf_arr | bp_i)
  end

(*------------------------------------------------------------------*)

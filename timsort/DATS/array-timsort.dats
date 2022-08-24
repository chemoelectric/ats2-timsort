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

#define WORKSPACE_THRESHOLD 256
#define STK_MAX_THRESHOLD 64   (* The bitsize of a size_t on AMD64. *)

macdef orelse1 (a, b) = (if ,(a) then true else ,(b))
infix ( || ) |||
macdef ||| = orelse1

macdef andalso1 (a, b) = (if ,(a) then ,(b) else false)
infix ( && ) &&&
macdef &&& = andalso1

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
   bptr_anchor (a, p_arr),
   bptr (a, p_arr, runlen),
   bptr (a, p_arr, n)) -< !wrt >
    void

(* Find a monotonically non-descending run or a monotonically
   descending run, and convert it to a monotonically non-descending
   run. That is, into a sorted run. *)
extern fn {a : vt@ype}
sort_a_monotonic_run :
  {p_arr : addr}
  {n     : pos}
  (!array_v (a, p_arr, n) |
   bptr_anchor (a, p_arr),
   bptr (a, p_arr, n)) -< !wrt >
    [runlen : pos | runlen <= n]
    bptr (a, p_arr, runlen)

(*------------------------------------------------------------------*)

implement {}
minimum_run_length n =
  if n < i2sz 64 then
    n       (* The array to be sorted is small. Use insertion sort. *)
  else
    (* The algorithm here is similar to that used in Python’s
       listsort, and tries to divide up n into a number of runs that
       is either a power of two or is close to but less than a power
       of two.
       
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
                                        (pf_arr |
                                         bp_arr, bp_i, bp_n) =
  (* A stable binary insertion sort. *)
  let
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

implement {a}
sort_a_monotonic_run {p_arr} {n} (pf_arr | bp_arr, bp_n) =
  let
    val bp_i = bptr_succ<a> bp_arr
  in
    if bp_i = bp_n then
      bp_i                      (* A run of one. *)
    else if elem_lt<a> (pf_arr | bp_i, bp_arr) then
      let                       (* A descending run. *)
        fun
        loop {i : pos | i <= n}
             .<n - i>.
             (pf_arr : !array_v (a, p_arr, n) |
              bp_i   : bptr (a, p_arr, i))
            :<> [i1 : pos | i1 <= n]
                bptr (a, p_arr, i1) =
          if bp_i = bp_n then
            bp_i
          else if elem_lt<a> (pf_arr | bp_i, bptr_pred<a> bp_i) then
            loop (pf_arr | bptr_succ<a> bp_i)
          else
            bp_i

          val bp_i = loop (pf_arr | bptr_succ<a> bp_i)
      in
        subreverse<a> (pf_arr | bp_arr, bp_i);
        bp_i
      end
    else
      let                       (* A non-descending run. *)
        fun
        loop {i : pos | i <= n}
             .<n - i>.
             (pf_arr : !array_v (a, p_arr, n) |
              bp_i   : bptr (a, p_arr, i))
            :<> [i1 : pos | i1 <= n]
                bptr (a, p_arr, i1) =
          if bp_i = bp_n then
            bp_i
          else if elem_lt<a> (pf_arr | bp_i, bptr_pred<a> bp_i) then
            bp_i
          else
            loop (pf_arr | bptr_succ<a> bp_i)
      in
        loop (pf_arr | bptr_succ<a> bp_i)
      end
  end

(*------------------------------------------------------------------*)

fn {a : vt@ype}
timsort_main
          {p_arr   : addr}
          {n       : int}
          {p_work  : addr}
          {worksz  : int | n <= 2 * worksz}
          {p_stk   : addr}
          {stk_max : pos}
          (pf_arr  : !array_v (a, p_arr, n),
           pf_work : !array_v (a?, p_work, worksz) |
           p_arr   : ptr p_arr,
           n       : size_t n,
           p_work  : ptr p_work,
           stk     : &stk_vt (p_stk, 0, stk_max))
    :<!wrt> void =
  ()                            (* FIXME *)

fn {a : vt@ype}
timsort_with_stk_on_stack
          {p_arr   : addr}
          {n       : int}
          {p_work  : addr}
          {worksz  : int | n <= 2 * worksz}
          (pf_arr  : !array_v (a, p_arr, n),
           pf_work : !array_v (a?, p_work, worksz) |
           p_arr   : ptr p_arr,
           n       : size_t n,
           p_work  : ptr p_work)
    :<!wrt> void =
  let
    var stk_storage =
      @[stk_entry_t][STK_MAX_THRESHOLD] (@(the_null_ptr, i2sz 0))
    var stk = stk_vt_make (view@ stk_storage |
                           addr@ stk_storage, i2sz STK_MAX_THRESHOLD)
    val () = timsort_main (pf_arr, pf_work | p_arr, n, p_work, stk)
    prval () = view@ stk_storage := stk.pf
  in
  end

fn {a : vt@ype}
timsort_with_stk_in_heap
          {p_arr   : addr}
          {n       : int}
          {p_work  : addr}
          {worksz  : int | n <= 2 * worksz}
          (pf_arr  : !array_v (a, p_arr, n),
           pf_work : !array_v (a?, p_work, worksz) |
           p_arr   : ptr p_arr,
           n       : size_t n,
           p_work  : ptr p_work)
    :<!wrt> void =
  let
    val () = $effmask_exn assertloc (i2sz 1 <= sizeof<size_t>)
    val @(pf_stk_storage, pfgc_stk_storage | p_stk_storage) =
      array_ptr_alloc<stk_entry_t> (sizeof<size_t>)
    val () =
      array_initize_elt<stk_entry_t>
        (!p_stk_storage, sizeof<size_t>, @(the_null_ptr, i2sz 0))
    var stk = stk_vt_make (pf_stk_storage |
                           p_stk_storage, sizeof<size_t>)
    val () = timsort_main (pf_arr, pf_work | p_arr, n, p_work, stk)
    val () = pf_stk_storage := stk.pf
    val () = array_ptr_free (pf_stk_storage, pfgc_stk_storage |
                             p_stk_storage)
  in
  end

fn {a : vt@ype}
timsort_providing_stk
          {p_arr   : addr}
          {n       : int}
          {p_work  : addr}
          {worksz  : int | n <= 2 * worksz}
          (pf_arr  : !array_v (a, p_arr, n),
           pf_work : !array_v (a?, p_work, worksz) |
           p_arr   : ptr p_arr,
           n       : size_t n,
           p_work  : ptr p_work)
    :<!wrt> void =
  if (char_bit () * sizeof<size_t> <= i2sz STK_MAX_THRESHOLD)
        ||| (iseqz (n >> STK_MAX_THRESHOLD)) then
    timsort_with_stk_on_stack (pf_arr, pf_work | p_arr, n, p_work)
  else
    timsort_with_stk_in_heap (pf_arr, pf_work | p_arr, n, p_work)

implement {a}
array_timsort_given_workspace {n} {arrsz} {worksz} (arr, n, work) =
  if n <= i2sz 1 then
    ()                          (* No sorting is needed. *)
  else
    let
      prval () = lemma_g1uint_param n

      val p_arr = addr@ arr
      and p_work = addr@ work

      prval [p_arr : addr] EQADDR () = eqaddr_make_ptr p_arr
      prval [p_work : addr] EQADDR () = eqaddr_make_ptr p_work

      prval @(pf_arr, pf_arr_unused) =
        array_v_split {a} {p_arr} {arrsz} {n} (view@ arr)
      prval pf_work = view@ work

      val () = timsort_providing_stk (pf_arr, pf_work |
                                      p_arr, n, p_work)

      prval () = view@ arr :=
        array_v_unsplit (pf_arr, pf_arr_unused)
      prval () = view@ work := pf_work
    in
    end

implement {a}
array_timsort_not_given_workspace {n} {arrsz} (arr, n) =
  let
    prval () = lemma_array_param arr
    prval () = lemma_g1uint_param n

    fn
    sort {n      : int}
         {arrsz  : int | n <= arrsz}
         {worksz : int | n <= 2 * worksz}
         (arr    : &array (a, arrsz),
          n      : size_t n,
          work   : &array (a?, worksz))
        :<!wrt> void =
      array_timsort_given_workspace<a> (arr, n, work)
  in
    if n <= i2sz 1 then
      ()                        (* No sorting is needed. *)
    else if n <= double (i2sz WORKSPACE_THRESHOLD) then
      let                       (* Put the workspace on the stack. *)
        var work : @[a?][WORKSPACE_THRESHOLD]
      in
        sort (arr, n, work)
      end
    else
      let                       (* Put the workspace in the heap. *)
        val worksz = n \ceildiv (i2sz 2)
        val @(pf_work, pfgc_work | p_work) =
          array_ptr_alloc<a?> worksz
      in
        sort (arr, n, !p_work);
        array_ptr_free (pf_work, pfgc_work | p_work)
      end
  end

(*------------------------------------------------------------------*)

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

(* Starting at position i, create a sorted array segment of at least
   minrun elements, or until the end of the array. *)
extern fn {a : vt@ype}
provide_a_sorted_run :
  {p_arr  : addr}
  {n      : pos}
  {i      : nat | i < n}
  {minrun : pos}
  (!array_v (a, p_arr, n) |
   bptr (a, p_arr, i),
   bptr (a, p_arr, n),
   size_t minrun) -< !wrt >
    [j : int | i < j; j <= n]
    bptr (a, p_arr, j)

extern fn {a : vt@ype}
merge_left :
  {p_arr  : addr}
  {n      : pos}
  {i      : nat | 2 * i <= n}
  {p_work : addr}
  {worksz : int | n <= 2 * worksz}
  (!array_v (a, p_arr, n),
   !array_v (a?, p_work, worksz) |
   bptr_anchor (a, p_arr),
   bptr (a, p_arr, i),
   bptr (a, p_arr, n),
   bptr_anchor (a?, p_work),
   &Size_t (* gallop_threshold *) ) -< !wrt >
    void

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
            bp_k - (half (bp_k - bp_j))
        in
          if elem_lt<a> (pf_arr | bp_i, bp_h) then
            loop (pf_arr | bp_j, pred bp_h)
          else
            loop (pf_arr | bp_h, bp_k)
        end
      else if bp_j <> bp_arr then
        succ bp_j
      else if elem_lt<a> (pf_arr | bp_i, bp_arr) then
        bp_arr
      else
        succ bp_arr
  in
    loop (pf_arr | bp_arr, pred bp_i)
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
          loop (pf_arr | succ bp_i)
        end
  in
    loop (pf_arr | bp_i)
  end

(*------------------------------------------------------------------*)

implement {a}
sort_a_monotonic_run {p_arr} {n} (pf_arr | bp_arr, bp_n) =
  let
    val bp_i = succ bp_arr
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
          else if elem_lt<a> (pf_arr | bp_i, pred bp_i) then
            loop (pf_arr | succ bp_i)
          else
            bp_i

          val bp_i = loop (pf_arr | succ bp_i)
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
          else if elem_lt<a> (pf_arr | bp_i, pred bp_i) then
            bp_i
          else
            loop (pf_arr | succ bp_i)
      in
        loop (pf_arr | succ bp_i)
      end
  end

(*------------------------------------------------------------------*)

implement {a}
provide_a_sorted_run {p_arr} {n} {i} (pf_arr | bp_i, bp_n, minrun) =
  let
    val minrun = min (minrun, bp_n - bp_i)
    prval [minrun : int] EQINT () = eqint_make_guint minrun

    (* Isolate the part of the array to be sorted. *)
    prval @(pf_arr0, pf_arr1_) =
      array_v_split {a} {p_arr} {n} {i} pf_arr
    prval @(pf_arr1, pf_arr2) =
      array_v_split {a} {p_arr + (i * sizeof a)} {n - i} {minrun}
                    pf_arr1_

    (* We will sort from bp_i to bp_i + minrun. *)
    val bp_arr1 = bptr_reanchor<a> bp_i
    val bp_minrun = bp_arr1 + minrun

    (* The actual sorting. *)
    val bp_runlen =
      sort_a_monotonic_run<a>
        (pf_arr1 | bp_arr1, bp_minrun)
    val () =
      insertion_sort_given_initial_sorted_run<a>
        (pf_arr1 | bp_arr1, bp_runlen, bp_minrun)

    (* Reconstruct the array. *)
    prval () = pf_arr :=
      array_v_unsplit (pf_arr0, array_v_unsplit (pf_arr1, pf_arr2))
  in
    bp_i + minrun
  end

(*------------------------------------------------------------------*)

fn {a : vt@ype}
scan_R_lt_L_for_merge_left
          {p_rgt    : addr}
          {i, n_rgt : nat | i <= n_rgt}
          {p_L      : addr}
          (pf_rgt   : !array_v (a, p_rgt, n_rgt),
           pf_L     : !a @ p_L |
           bp_R     : bptr (a, p_rgt, i),
           bp_n_rgt : bptr (a, p_rgt, n_rgt),
           bp_L     : bptr_anchor (a, p_L))
    :<> [i1 : int | i <= i1; i1 <= n_rgt]
        bptr (a, p_rgt, i1) =
  let
    fun
    loop {i0 : nat | i <= i0; i0 <= n_rgt}
         .<n_rgt - i0>.
         (pf_rgt : !array_v (a, p_rgt, n_rgt),
          pf_L   : !a @ p_L |
          bp_R0  : bptr (a, p_rgt, i0))
        :<> [i1 : int | i0 <= i1; i1 <= n_rgt]
            bptr (a, p_rgt, i1) =
      if bp_R0 = bp_n_rgt then
        bp_R0
      else
        let
          prval @(pf_rgt1, pf_rgt2) =
            array_v_split {a} {p_rgt} {n_rgt} {i0} pf_rgt
          prval @(pf_R0, pf_rgt3) = array_v_uncons pf_rgt2
          val R0_lt_L =
            elem_lt<a> (pf_R0, pf_L | bptr2ptr bp_R0, bptr2ptr bp_L)
          prval () = pf_rgt :=
            array_v_unsplit (pf_rgt1, array_v_cons (pf_R0, pf_rgt3))
        in
          if R0_lt_L then
            loop (pf_rgt, pf_L | succ bp_R0)
          else
            bp_R0
        end
  in
    loop (pf_rgt, pf_L | bp_R)
  end

fn {a : vt@ype}
scan_L_lte_R_for_merge_left
          {p_R      : addr}
          {p_lft    : addr}
          {j, n_lft : nat | j <= n_lft}
          (pf_R     : !a @ p_R,
           pf_lft   : !array_v (a, p_lft, n_lft) |
           bp_R     : bptr_anchor (a, p_R),
           bp_L     : bptr (a, p_lft, j),
           bp_n_lft : bptr (a, p_lft, n_lft))
    :<> [j1 : int | j <= j1; j1 <= n_lft]
        bptr (a, p_lft, j1) =
  let
    fun
    loop {j0 : nat | j <= j0; j0 <= n_lft}
         .<n_lft - j0>.
         (pf_R     : !a @ p_R,
          pf_lft   : !array_v (a, p_lft, n_lft) |
          bp_L0    : bptr (a, p_lft, j0))
        :<> [j1 : int | j0 <= j1; j1 <= n_lft]
            bptr (a, p_lft, j1) =
      if bp_L0 = bp_n_lft then
        bp_L0
      else
        let
          prval @(pf_lft1, pf_lft2) =
            array_v_split {a} {p_lft} {n_lft} {j0} pf_lft
          prval @(pf_L0, pf_lft3) = array_v_uncons pf_lft2
          val R_lt_L0 =
            elem_lt<a> (pf_R, pf_L0 | bptr2ptr bp_R, bptr2ptr bp_L0)
          prval () = pf_lft :=
            array_v_unsplit (pf_lft1, array_v_cons (pf_L0, pf_lft3))
        in
          if R_lt_L0 then
            bp_L0
          else
            loop (pf_R, pf_lft | succ bp_L0)
        end
  in
    loop (pf_R, pf_lft | bp_L)
  end

(*
implement {a}
merge_left {p_arr} {n} {i} {p_work} {worksz}
           (pf_arr, pf_work | bp_arr, bp_i, bp_n, bp_work,
                              gallop_threshold) =
  let
    prval @(pf_left, pf_right) =
      array_v_split {a} {p_arr} {n} {i} pf_arr
    prval @(pf_temp, pf_unused) =
      array_v_split {a?} {p_work} {worksz} {i} pf_work

    stadef p_temp = p_work
    stadef tempsz = i

    val () = copy<a> (pf_temp, pf_left | bp_work, bp_arr, bp_i)

    val bp_temp : bptr_anchor (a, p_temp) =
      ptr2bptr_anchor (bptr2ptr bp_work)
    val bp_tempsz : bptr (a, p_temp, tempsz) =
      bp_temp + (bp_i - bp_arr)
      
    prval pf_merged = array_v_nil {a} {p_arr} ()
    prval pf_between = pf_left
    prval pf_cleared = array_v_nil {a?} {p_temp} ()

    fun
    merge_runs
              {n_merged   : nat}
              {j          : nat | n_merged <= j; j <= n;
                                  n - j <= n_merged}
              {n_cleared  : int | n_cleared == n_merged - (n - j)}
              .<n - n_merged>.
              (pf_merged  : array_v (a, p_arr, n_merged),
               pf_between : array_v (a?,
                                     p_arr + (sizeof a * n_merged),
                                     j - n_merged),
               pf_rgt     : array_v (a, p_arr + (sizeof a * j),
                                     n - j),
               pf_cleared : array_v (a?, p_temp, n_cleared),
               pf_lft     : array_v (a,
                                     p_temp + (sizeof a * n_cleared),
                                     tempsz - n_cleared) |
               bp_between : bptr (a?, p_arr, n_merged),
               bp_rgt     : bptr (a, p_arr, j),
               bp_lft     : bptr (a, p_temp, n_cleared))
        :<!wrt> @(array_v (a, p_arr, n),
                  array_v (a?, p_temp, tempsz) | ) =
      (* FIXME: FOR NOW, THIS IS JUST A SIMPLE MERGE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
      (* FIXME: and not the most efficient one. *)
      if bp_between = bp_n then
        let
          prval () = array_v_unnil pf_between
          prval () = array_v_unnil pf_rgt
          prval () = array_v_unnil pf_lft
        in
          @(pf_merged, pf_cleared | )
        end
      else
        let
          prval @(pf_R, pf_rgt1) = array_v_uncons pf_rgt
          prval @(pf_L, pf_lft1) = array_v_uncons pf_lft
        in
          if elem_lt<a> (pf_R, pf_L | bp_rgt, bp_lft) then
            let
              val [i_R1 : int] bp_R1 =
                scan_R_lt_L_for_merge_left<a>
                  (pf_rgt1, pf_L | succ bp_rgt, bp_n,
                                   bptr_reanchor bp_lft)

              prval @(pf_rgt0, pf_rgt1) =
                array_v_split {a} {p_arr + (sizeof a * j)}
                              {n - j} {i_R1 - j}
                              (array_v_cons (pf_R, pf_rgt1))
              prval @(pf_between0, pf_between1) =
                array_v_split {a?} {p_arr + (sizeof a * n_merged)}
                              {j - n_merged} {i_R1 - j}
                              pf_between

              val () = copy<a> (pf_between0, pf_rgt0 |
                                bptr_reanchor bp_between,
                                bptr_reanchor bp_rgt,
                                bp_R1 - bp_rgt)

              prval pf_merged1 =
                array_v_unsplit (pf_merged, pf_between0)
              prval pf_between2 =
                array_v_unsplit (pf_between1, pf_rgt0)
            in
              merge_runs
                (pf_merged1, pf_between2, pf_rgt1,
                 pf_cleared, array_v_cons (pf_L, pf_lft1) |
                 bp_between + (bp_R1 - bp_rgt), bp_R1, bp_lft)
            end
          else
            let
              val [i_L1 : int] bp_L1 =
                scan_L_lte_R_for_merge_left<a>
                  (pf_R, pf_lft1 | bptr_reanchor bp_rgt,
                                   succ bp_lft, bp_tempsz)

              prval @(pf_lft0, pf_lft1) =
                array_v_split {a} {p_temp + (sizeof a * n_cleared)}
                              {tempsz - n_cleared} {i_L1 - n_cleared}
                              (array_v_cons (pf_L, pf_lft1))
              prval @(pf_between0, pf_between1) =
                array_v_split {a?} {p_arr + (sizeof a * n_merged)}
                              {j - n_merged} {i_L1 - j}
                              pf_between

              val () = copy<a> (pf_between0, pf_lft0 |
                                bptr_reanchor bp_between,
                                bptr_reanchor bp_lft,
                                bp_L1 - bp_lft)

              prval pf_merged1 =
                array_v_unsplit (pf_merged, pf_between0)
              prval pf_cleared1 =
                array_v_unsplit (pf_cleared, pf_lft0)
            in
              merge_runs
                (pf_merged1, pf_between1,
                 array_v_cons (pf_R, pf_rgt1), pf_cleared1, pf_lft1 |
                 bp_between + (bp_L1 - bp_lft), bp_rgt, bp_L1)
            end
        end

    val @(pf_arr1, pf_temp1 | ) =
      merge_runs (pf_merged, pf_between, pf_right,
                  pf_cleared, pf_temp |
                  ptr2bptr_anchor (bptr2ptr bp_arr),
                  bp_i, bp_temp)

    prval () = pf_work := array_v_unsplit (pf_temp1, pf_unused)
    prval () = pf_arr := pf_arr1
  in
  end
*)

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
  let
    fn
    sort_main {p_arr   : addr}
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
      timsort_main<a> (pf_arr, pf_work | p_arr, n, p_work, stk)
  in
    if (char_bit () * sizeof<size_t> <= i2sz STK_MAX_THRESHOLD)
          ||| (iseqz (n >> STK_MAX_THRESHOLD)) then
      let                       (* Put stk on the system stack. *)
        var stk_storage =
          @[stk_entry_t][STK_MAX_THRESHOLD] (@(the_null_ptr, i2sz 0))
        var stk = stk_vt_make (view@ stk_storage |
                               addr@ stk_storage,
                               i2sz STK_MAX_THRESHOLD)
        val () = sort_main (pf_arr, pf_work | p_arr, n, p_work, stk)
        prval () = view@ stk_storage := stk.pf
      in
      end
    else
      let                       (* Put stk in the heap. *)
        val () = $effmask_exn assertloc (i2sz 1 <= sizeof<size_t>)
        val @(pf_stk_storage, pfgc_stk_storage | p_stk_storage) =
          array_ptr_alloc<stk_entry_t> (sizeof<size_t>)
        val () =
          array_initize_elt<stk_entry_t>
            (!p_stk_storage, sizeof<size_t>, @(the_null_ptr, i2sz 0))
        var stk = stk_vt_make (pf_stk_storage |
                               p_stk_storage, sizeof<size_t>)
        val () = sort_main (pf_arr, pf_work | p_arr, n, p_work, stk)
        val () = pf_stk_storage := stk.pf
        val () = array_ptr_free (pf_stk_storage, pfgc_stk_storage |
                                 p_stk_storage)
      in
      end
  end

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

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
          {p, q   : addr}
          {i, j   : int}
          (pf_i   : !a @ (p + (i * sizeof a)),
           pf_j   : !a @ (q + (j * sizeof a)) |
           bp_i   : bptr (a, p, i),
           bp_j   : bptr (a, q, j))
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
(* Galloping searches.                                              *)

typedef find_pos_t (a : vt@ype) =
  {p_arr : addr}
  {n     : pos}
  {hint  : nat | hint <= n - 1}
  {p_x0  : addr}
  {n_x0  : int}
  {i_x   : nat | i_x <= n_x0 - 1}
  (!array_v (a, p_arr, n),
   !array_v (a, p_x0, n_x0) |
   bptr_anchor (a, p_arr),
   bptr (a, p_arr, n),
   size_t hint,
   bptr (a, p_x0, i_x)) -<>
    [j : nat | j <= n]
    bptr (a, p_arr, j)

extern fn {a : vt@ype}
find_1st_position_past_satisfiespred$pred :
  {p, q : addr}
  (!a @ p, !a @ q | ptr p, ptr q) -<> bool

extern fn {a : vt@ype}
find_1st_position_past_satisfiespred :
  find_pos_t a

extern fn {a : vt@ype}
find_1st_position_past_lt_x :
  find_pos_t a

extern fn {a : vt@ype}
find_1st_position_past_lte_x :
  find_pos_t a

fn {a : vt@ype}
next_pointer_rightwards
          {p_arr  : addr}
          {n      : int}
          {i, j   : nat | i <= j; j < n - 1}
          (bp_arr : bptr_anchor (a, p_arr),
           bp_n   : bptr (a, p_arr, n),
           bp_i   : bptr (a, p_arr, i),
           bp_j   : bptr (a, p_arr, j))
    :<> [j1 : nat | j < j1; j1 <= n - 1]
        bptr (a, p_arr, j1) =
  if bp_i = bp_j then
    succ bp_j
  else
    let
      val bp_n1 = pred bp_n
      and j = bp_j - bp_arr
      and diff = bp_j - bp_i
      val diff1 = double diff
    in
      if (diff1 < diff) + (j + diff1 < j) then
        (* Overflow. *)
        bp_n1
      else if bp_n1 - bp_arr <= j + diff1 then
        bp_n1
      else
        bp_j + diff1
    end

fn {a : vt@ype}
next_pointer_leftwards
          {p_arr  : addr}
          {n      : int}
          {i, j   : pos | i <= j; j <= n - 1}
          (bp_arr : bptr_anchor (a, p_arr),
           bp_n   : bptr (a, p_arr, n),
           bp_i   : bptr (a, p_arr, i),
           bp_j   : bptr (a, p_arr, j))
    :<> [i1 : nat | i1 < i]
        bptr (a, p_arr, i1) =
  if bp_i = bp_j then
    pred bp_i
  else
    let
      val i = bp_i - bp_arr
      and diff = bp_j - bp_i
      val diff1 = double diff
    in
      if diff1 < diff then
        (* Overflow. *)
        bp_arr
      else if i <= diff1 then
        bp_arr
      else
        bp_i - diff1
    end

implement {a}
find_1st_position_past_satisfiespred
          {p_arr} {n} {hint} {p_x0} {n_x0} {i_x}
          (pf_arr, pf_x0 | bp_arr, bp_n, hint, bp_x) =
  let
    macdef order_pred =
      find_1st_position_past_satisfiespred$pred<a>

    fn {}
    elem_pred {k : nat | k <= n - 1}
              (pf_arr : !array_v (a, p_arr, n),
               pf_x0  : !array_v (a, p_x0, n_x0) |
               bp_k   : bptr (a, p_arr, k))
        :<> bool =
      let
        prval @(pf_k, fpf_k) =
          array_v_takeout {a} {p_arr} {n} {k} pf_arr
        prval @(pf_x, fpf_x) =
          array_v_takeout {a} {p_x0} {n_x0} {i_x} pf_x0

        val satisfies =
          order_pred (pf_k, pf_x | bptr2ptr bp_k, bptr2ptr bp_x)

        prval () = pf_arr := fpf_k pf_k
        prval () = pf_x0 := fpf_x pf_x
      in
        satisfies
      end

    fun {}
    binary_search
              {i, j : nat | i <= j; j <= n - 1}
              .<j - i>.
              (pf_arr : !array_v (a, p_arr, n),
               pf_x0  : !array_v (a, p_x0, n_x0) |
               bp_i   : bptr (a, p_arr, i),
               bp_j   : bptr (a, p_arr, j))
        :<> [k : nat | i <= k; k <= j]
            bptr (a, p_arr, k) =
      if bp_i = bp_j then
        bp_i
      else
        let
          val bp_h = bp_i + half (bp_j - bp_i)
        in
          if elem_pred (pf_arr, pf_x0 | bp_h) then
            binary_search (pf_arr, pf_x0 | succ bp_h, bp_j)
          else
            binary_search (pf_arr, pf_x0 | bp_i, bp_h)
        end

    fun {}
    gallop_rightwards
              {i, j : nat | i <= j; j <= n - 1}
              .<n - j>.
              (pf_arr : !array_v (a, p_arr, n),
               pf_x0  : !array_v (a, p_x0, n_x0) |
               bp_i   : bptr (a, p_arr, i),
               bp_j   : bptr (a, p_arr, j))
        :<> [k : nat | i < k; k <= n]
            bptr (a, p_arr, k) =
      if bp_j = pred bp_n then
        bp_n
      else
        let
          val bp_j = next_pointer_rightwards<a> (bp_arr, bp_n,
                                                 bp_i, bp_j)
          and bp_i = bp_j
        in
          if elem_pred (pf_arr, pf_x0 | bp_j) then
            gallop_rightwards (pf_arr, pf_x0 | bp_i, bp_j)
          else
            binary_search (pf_arr, pf_x0 | succ bp_i, bp_j)
        end

    fun {}
    gallop_leftwards
              {i, j : nat | i <= j; j <= n - 1}
              .<i>.
              (pf_arr : !array_v (a, p_arr, n),
               pf_x0  : !array_v (a, p_x0, n_x0) |
               bp_i   : bptr (a, p_arr, i),
               bp_j   : bptr (a, p_arr, j))
        :<> [k : nat | k <= i]
            bptr (a, p_arr, k) =
      if bp_i = bp_arr then
        bp_arr
      else
        let
          val bp_i = next_pointer_leftwards<a> (bp_arr, bp_n,
                                                bp_i, bp_j)
          and bp_j = bp_i
        in
          if elem_pred (pf_arr, pf_x0 | bp_i) then
            binary_search (pf_arr, pf_x0 | succ bp_i, bp_j)
          else
            gallop_leftwards (pf_arr, pf_x0 | bp_i, bp_j)
        end

    val bp_hint = bp_arr + hint
  in
    if elem_pred (pf_arr, pf_x0 | bp_hint) then
      gallop_rightwards (pf_arr, pf_x0 | bp_hint, bp_hint)
    else
      gallop_leftwards (pf_arr, pf_x0 | bp_hint, bp_hint)
  end

implement {a}
find_1st_position_past_lt_x
          {p_arr} {n} {hint} {p_x0} {n_x0} {i_x}
          (pf_arr, pf_x0 | bp_arr, bp_n, hint, bp_x) =
  let
    implement
    find_1st_position_past_satisfiespred$pred<a>
               (pf_p, pf_q | p, q) =
      elem_lt<a> (pf_p, pf_q | p, q)
  in
    find_1st_position_past_satisfiespred<a>
      {p_arr} {n} {hint} {p_x0} {n_x0} {i_x}
      (pf_arr, pf_x0 | bp_arr, bp_n, hint, bp_x)
  end

implement {a}
find_1st_position_past_lte_x
          {p_arr} {n} {hint} {p_x0} {n_x0} {i_x}
          (pf_arr, pf_x0 | bp_arr, bp_n, hint, bp_x) =
  let
    implement
    find_1st_position_past_satisfiespred$pred<a>
               (pf_p, pf_q | p, q) =
      ~elem_lt<a> (pf_q, pf_p | q, p)
  in
    find_1st_position_past_satisfiespred<a>
      {p_arr} {n} {hint} {p_x0} {n_x0} {i_x}
      (pf_arr, pf_x0 | bp_arr, bp_n, hint, bp_x)
  end

(*------------------------------------------------------------------*)
(* Merges.                                                          *)

vtypedef merge_params_vt =
  @{
    gallop_start_threshold = [t : pos] size_t t,
    gallop_stop_threshold = [t : pos] size_t t
  }

fn {}
initialize_gallop_thresholds
          (params : &merge_params_vt? >> merge_params_vt)
    :<!wrt> void =
  begin
    params.gallop_start_threshold := i2sz 7;
    params.gallop_stop_threshold := i2sz 7
  end

fn {}
lower_gallop_thresholds
          (params : &merge_params_vt)
    :<!wrt> void =
  let
    val start_threshold0 = params.gallop_start_threshold
    val start_threshold1 = max (i2sz 1, pred start_threshold0)
    val stop_threshold0 = params.gallop_stop_threshold
    val stop_threshold1 = max (i2sz 1, pred stop_threshold0)
  in
    params.gallop_start_threshold := start_threshold1;
    params.gallop_stop_threshold := stop_threshold1
  end

fn {}
raise_gallop_thresholds
          (params : &merge_params_vt)
    :<!wrt> void =
  let
    val start_threshold0 = params.gallop_start_threshold
    val start_threshold1 = succ start_threshold0
    val stop_threshold0 = params.gallop_stop_threshold
    val stop_threshold1 = succ stop_threshold0
  in
    params.gallop_start_threshold := start_threshold1;
    params.gallop_stop_threshold := stop_threshold1
  end

extern fn {a : vt@ype}
merge_left :
  {p_arr  : addr}
  {n      : pos}
  {i      : nat | 2 * i <= n}
  {p_work : addr}
  {worksz : int | i <= worksz}
  (!array_v (a, p_arr, n),
   !array_v (a?, p_work, worksz) |
   bptr_anchor (a, p_arr),
   bptr (a, p_arr, i),
   bptr (a, p_arr, n),
   bptr_anchor (a?, p_work),
   &merge_params_vt >> _) -< !wrt >
    void

implement {a}
merge_left {p_arr} {n} {i} {p_work} {worksz}
           (pf_arr, pf_work | bp_arr, bp_i, bp_n, bp_work, params) =
  let
    stadef pntr (p : addr, i : int) = p + (i * sizeof a)

    (* Split the array into left and right, and copy the left to
       workspace. *)
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

    fn {}
    left_is_done
              {i_rgt      : nat | i_rgt <= n}
              (pf_merged  : !array_v (a, p_arr, i_rgt)
                              >> array_v (a, p_arr, n),
               pf_between : !array_v (a?, pntr (p_arr, i_rgt), 0)
                              >> void,
               pf_rgt     : !array_v (a, pntr (p_arr, i_rgt),
                                      n - i_rgt)
                              >> void,
               pf_lft     : !array_v (a, pntr (p_temp, tempsz), 0)
                              >> void | )
          :<> void =
        (* This routine generates no executable code, and could have
           been written as a prfn. *)
        let
          (* Any remaining right entries already are in place. *)
          prval () = pf_lft := array_v_unnil pf_lft
          prval () = pf_between := array_v_unnil pf_between
          prval () = pf_merged := array_v_unsplit (pf_merged, pf_rgt)
          prval () = pf_rgt := ()
        in
        end

    fn
    right_is_done
              {i_between : nat | i_between <= n}
              {i_lft     : nat | n - i_between == tempsz - i_lft}
              (pf_merged  : !array_v (a, p_arr, i_between)
                              >> array_v (a, p_arr, n),
               pf_between : !array_v (a?, pntr (p_arr, i_between),
                                      n - i_between) >> void,
               pf_rgt     : !array_v (a, pntr (p_arr, n), 0) >> void,
               pf_cleared : !array_v (a?, p_temp, i_lft)
                              >> array_v (a?, p_temp, tempsz),
               pf_lft     : !array_v (a, pntr (p_temp, i_lft),
                                      tempsz - i_lft) >> void |
               bp_between : bptr (a?, p_arr, i_between),
               bp_lft     : bptr (a, p_temp, i_lft))
          :<!wrt> void =
        let                   (* Copy any remaining left entries. *)
          prval () = pf_rgt := array_v_unnil pf_rgt
          val () = copy<a> (pf_between, pf_lft |
                            bptr_reanchor bp_between,
                            bptr_reanchor bp_lft,
                            bp_tempsz - bp_lft)
          prval () = pf_merged := array_v_unsplit (pf_merged,
                                                   pf_between)
          prval () = pf_between := ()
          prval () = pf_cleared := array_v_unsplit (pf_cleared,
                                                    pf_lft)
          prval () = pf_lft := ()
        in
        end

    fnx
    merge_runs
              {i_between : nat}
              {i_rgt     : nat | i_between <= i_rgt; i_rgt <= n}
              {i_lft     : nat | i_lft <= tempsz;
                                 i_rgt - i_between == tempsz - i_lft}
              .<n - i_between>.
              (pf_merged  : !array_v (a, p_arr, i_between)
                              >> array_v (a, p_arr, n),
               pf_between : !array_v (a?, pntr (p_arr, i_between),
                                      i_rgt - i_between) >> void,
               pf_rgt     : !array_v (a, pntr (p_arr, i_rgt),
                                      n - i_rgt) >> void,
               pf_cleared : !array_v (a?, p_temp, i_lft)
                              >> array_v (a?, p_temp, tempsz),
               pf_lft     : !array_v (a, pntr (p_temp, i_lft),
                                      tempsz - i_lft) >> void |
               bp_between : bptr (a?, p_arr, i_between),
               bp_rgt     : bptr (a, p_arr, i_rgt),
               bp_lft     : bptr (a, p_temp, i_lft),
               count_lft  : Size_t,
               count_rgt  : Size_t,
               params     : &merge_params_vt >> _)
        :<!wrt> void =
      if bp_lft = bp_tempsz then
        let
          prval () = lemma_mul_isfun {i_between, sizeof a}
                                     {i_rgt, sizeof a} ()
          prval () = lemma_mul_isfun {i_lft, sizeof a}
                                     {tempsz, sizeof a} ()
        in
          left_is_done {i_rgt}
                       (pf_merged, pf_between, pf_rgt, pf_lft | )
        end
      else if bp_rgt = bp_n then
        let
          prval () = lemma_mul_isfun {i_rgt, sizeof a}
                                     {n, sizeof a} ()
        in
          right_is_done {i_between} {i_lft}
                        (pf_merged, pf_between, pf_rgt,
                         pf_cleared, pf_lft |
                         bp_between, bp_lft)
        end
      else
        let
          prval @(pf_taken, pf_between1) = array_v_uncons pf_between
          prval @(pf_R, pf_rgt1) = array_v_uncons pf_rgt
          prval @(pf_L, pf_lft1) = array_v_uncons pf_lft
        in
          if elem_lt<a> (pf_R, pf_L | bp_rgt, bp_lft) then
            let                 (* R < L. Take R. *)
              prval () = pf_lft := array_v_cons (pf_L, pf_lft1)
              val x = bptr_get<a> (pf_R | bp_rgt)
              val () = ptr_set<a> (pf_taken | bptr2ptr bp_between, x)
              prval () = pf_merged :=
                array_v_extend (pf_merged, pf_taken)
              prval () = pf_between :=
                array_v_extend (pf_between1, pf_R)
              prval () = pf_rgt := pf_rgt1
              val bp_between = succ bp_between
              and bp_rgt = succ bp_rgt
              and count_lft = i2sz 0
              and count_rgt = succ count_rgt
            in
              if count_rgt >= (params.gallop_start_threshold) then
                galloping_merge (pf_merged, pf_between, pf_rgt,
                                 pf_cleared, pf_lft |
                                 bp_between, bp_rgt, bp_lft, params)
              else
                merge_runs (pf_merged, pf_between, pf_rgt,
                            pf_cleared, pf_lft |
                            bp_between, bp_rgt, bp_lft,
                            count_lft, count_rgt, params)
            end
          else
            let                 (* L <= R. Take L. *)
              prval () = pf_rgt := array_v_cons (pf_R, pf_rgt1)
              val x = bptr_get<a> (pf_L | bp_lft)
              val () = ptr_set<a> (pf_taken | bptr2ptr bp_between, x)
              prval () = pf_merged :=
                array_v_extend (pf_merged, pf_taken)
              prval () = pf_between := pf_between1
              prval () = pf_cleared :=
                array_v_extend (pf_cleared, pf_L)
              prval () = pf_lft := pf_lft1
              val bp_between = succ bp_between
              and bp_lft = succ bp_lft
              and count_lft = succ count_lft
              and count_rgt = i2sz 0
            in
              if count_lft >= (params.gallop_start_threshold) then
                galloping_merge (pf_merged, pf_between, pf_rgt,
                                 pf_cleared, pf_lft |
                                 bp_between, bp_rgt, bp_lft, params)
              else
                merge_runs (pf_merged, pf_between, pf_rgt,
                            pf_cleared, pf_lft |
                            bp_between, bp_rgt, bp_lft,
                            count_lft, count_rgt, params)
            end
        end
    and
    galloping_merge
              {i_between : nat}
              {i_rgt     : nat | i_between <= i_rgt; i_rgt <= n}
              {i_lft     : nat | i_lft <= tempsz;
                                 i_rgt - i_between == tempsz - i_lft}
              .<n - i_between>.
              (pf_merged  : !array_v (a, p_arr, i_between)
                              >> array_v (a, p_arr, n),
               pf_between : !array_v (a?, pntr (p_arr, i_between),
                                      i_rgt - i_between) >> void,
               pf_rgt     : !array_v (a, pntr (p_arr, i_rgt),
                                      n - i_rgt) >> void,
               pf_cleared : !array_v (a?, p_temp, i_lft)
                              >> array_v (a?, p_temp, tempsz),
               pf_lft     : !array_v (a, pntr (p_temp, i_lft),
                                      tempsz - i_lft) >> void |
               bp_between : bptr (a?, p_arr, i_between),
               bp_rgt     : bptr (a, p_arr, i_rgt),
               bp_lft     : bptr (a, p_temp, i_lft),
               params     : &merge_params_vt >> _)
        :<!wrt> void =
      if bp_lft = bp_tempsz then
        let
          prval () = lemma_mul_isfun {i_between, sizeof a}
                                     {i_rgt, sizeof a} ()
          prval () = lemma_mul_isfun {i_lft, sizeof a}
                                     {tempsz, sizeof a} ()
        in
          left_is_done {i_rgt}
                       (pf_merged, pf_between, pf_rgt, pf_lft | )
        end
      else if bp_rgt = bp_n then
        let
          prval () = lemma_mul_isfun {i_rgt, sizeof a}
                                     {n, sizeof a} ()
        in
          right_is_done {i_between} {i_lft}
                        (pf_merged, pf_between, pf_rgt,
                         pf_cleared, pf_lft |
                         bp_between, bp_lft)
        end
      else
        let
          prval () = prop_verify {i_between < i_rgt} ()
          prval () = prop_verify {i_rgt < n} ()

          (* Find a position within the left side data. *)
          val bp_lft0 = bptr_reanchor bp_lft
          val bp_n_lft0 = bp_lft0 + (bp_tempsz - bp_lft)
          val [count_lft : int] bp =
            find_1st_position_past_lte_x
              {pntr (p_temp, i_lft)} {tempsz - i_lft} {0}
              {pntr (p_arr, i_rgt)} {n - i_rgt} {0}
              (pf_lft, pf_rgt | bp_lft0, bp_n_lft0, i2sz 0,
                                bptr_reanchor bp_rgt)

          (* This is how much to copy. *)
          val count_lft : size_t count_lft = bp - bp_lft0

          (* Copy the data. *)
          prval @(pf_between1, pf_between2) =
            array_v_split {a?} {pntr (p_arr, i_between)}
                          {i_rgt - i_between} {count_lft}
                          pf_between
          prval @(pf_lft1, pf_lft2) =
            array_v_split {a} {pntr (p_temp, i_lft)}
                          {tempsz - i_lft} {count_lft}
                          pf_lft
          val () = copy<a> (pf_between1, pf_lft1 |
                            bptr_reanchor bp_between,
                            bp_lft0, count_lft)
          prval () = pf_merged :=
            array_v_unsplit (pf_merged, pf_between1)
          prval () = pf_between := pf_between2
          prval () = pf_cleared :=
            array_v_unsplit (pf_cleared, pf_lft1)
          prval () = pf_lft := pf_lft2

          stadef i_between = i_between + count_lft
          stadef i_lft = i_lft + count_lft
          val bp_between = bp_between + count_lft
          and bp_lft = bp_lft + count_lft
        in
          if bp_lft = bp_tempsz then
            let
              prval () = lemma_mul_isfun {i_between, sizeof a}
                                         {i_rgt, sizeof a} ()
              prval () = lemma_mul_isfun {i_lft, sizeof a}
                                         {tempsz, sizeof a} ()
            in
              if (count_lft >= (params.gallop_stop_threshold))
                    + (succ (bp_n - bp_rgt)
                          >= (params.gallop_stop_threshold)) then
                lower_gallop_thresholds params
              else
                raise_gallop_thresholds params;

              left_is_done {i_rgt}
                           (pf_merged, pf_between, pf_rgt, pf_lft | )
            end
          else
            let
              (* Copy the right side element whose position has been
                 found. *)
              prval @(pf_taken, pf_between1) =
                array_v_uncons pf_between
              prval @(pf_R, pf_rgt1) = array_v_uncons pf_rgt
              val x = bptr_get<a> (pf_R | bp_rgt)
              val () = ptr_set<a> (pf_taken | bptr2ptr bp_between, x)
              prval () = pf_merged :=
                array_v_extend (pf_merged, pf_taken)
              and () = pf_between :=
                array_v_extend (pf_between1, pf_R)
              and () = pf_rgt := pf_rgt1

              stadef i_between = i_between + 1
              stadef i_rgt = i_rgt + 1
              val bp_between = succ bp_between
              and bp_rgt = succ bp_rgt
            in
              if bp_rgt = bp_n then
                let
                  prval () = lemma_mul_isfun {i_rgt, sizeof a}
                                             {n, sizeof a} ()
                in
                  if count_lft >= (params.gallop_stop_threshold) then
                    lower_gallop_thresholds params
                  else
                    raise_gallop_thresholds params;

                  right_is_done {i_between} {i_lft}
                                (pf_merged, pf_between, pf_rgt,
                                 pf_cleared, pf_lft |
                                 bp_between, bp_lft)
                end
              else
                let
                  (* Find a position within the right side data. *)
                  val bp_rgt0 = bptr_reanchor bp_rgt
                  val bp_n_rgt0 = bp_rgt0 + (bp_n - bp_rgt)
                  val [count_rgt : int] bp =
                    find_1st_position_past_lt_x
                      {pntr (p_arr, i_rgt)} {n - i_rgt} {0}
                      {pntr (p_temp, i_lft)} {tempsz - i_lft} {0}
                      (pf_rgt, pf_lft | bptr_reanchor bp_rgt0,
                                        bp_n_rgt0, i2sz 0,
                                        bptr_reanchor bp_lft)

                  (* This is how much to copy. *)
                  val count_rgt : size_t count_rgt =
                    bp - bptr_reanchor bp_rgt0

                  (* Copy the data. *)
                  prval @(pf_rgt1, pf_rgt2) =
                    array_v_split {a} {pntr (p_arr, i_rgt)}
                                  {n - i_rgt} {count_rgt}
                                  pf_rgt
                  val bp_between0 = bptr_reanchor bp_between
                  val bp_rgt_src =
                    ptr2bptr_anchor (bptr2ptr bp_between0)
                        + (bp_rgt - bp_between)
                  val () =
                    move_left<a> {pntr (p_arr, i_between)}
                                 {i_rgt - i_between} {count_rgt}
                                 (pf_between, pf_rgt1 |
                                  bp_between0, bp_rgt_src, count_rgt)
                  prval () = pf_merged :=
                    array_v_unsplit (pf_merged, pf_between)
                  and () = pf_between := pf_rgt1
                  and () = pf_rgt := pf_rgt2

                  stadef i_between = i_between + count_rgt
                  stadef i_rgt = i_rgt + count_rgt
                  val bp_between = bp_between + count_rgt
                  and bp_rgt = bp_rgt + count_rgt

                  (* Copy the left side element whose position has been
                     found. *)
                  prval @(pf_taken, pf_between1) =
                    array_v_uncons pf_between
                  prval @(pf_L, pf_lft1) = array_v_uncons pf_lft
                  val x = bptr_get<a> (pf_L | bp_lft)
                  val () = ptr_set<a> (pf_taken |
                                       bptr2ptr bp_between, x)
                  prval () = pf_merged :=
                    array_v_extend (pf_merged, pf_taken)
                  and () = pf_between := pf_between1
                  and () = pf_cleared :=
                    array_v_extend (pf_cleared, pf_L)
                  and () = pf_lft := pf_lft1

                  stadef i_between = i_between + 1
                  stadef i_lft = i_lft + 1
                  val bp_between = succ bp_between
                  and bp_lft = succ bp_lft
                in
                  if (count_lft >= (params.gallop_stop_threshold))
                        + (count_rgt
                              >= (params.gallop_stop_threshold)) then
                    begin
                      (* Lower the gallop thresholds and continue
                         galloping. *)
                      lower_gallop_thresholds params;
                      galloping_merge (pf_merged, pf_between, pf_rgt,
                                       pf_cleared, pf_lft |
                                       bp_between, bp_rgt, bp_lft,
                                       params)
                    end
                  else
                    begin
                      (* Raise the gallop thresholds and stop
                         galloping. *)
                      raise_gallop_thresholds params;
                      merge_runs (pf_merged, pf_between, pf_rgt,
                                  pf_cleared, pf_lft |
                                  bp_between, bp_rgt, bp_lft,
                                  i2sz 0, i2sz 0, params)
                    end
                end
            end
        end

    prval pf_merged = array_v_nil {a} {p_arr} ()
    prval pf_between = pf_left
    prval pf_cleared = array_v_nil {a?} {p_temp} ()
    val () = merge_runs (pf_merged, pf_between, pf_right,
                         pf_cleared, pf_temp |
                         ptr2bptr_anchor (bptr2ptr bp_arr),
                         bp_i, bp_temp, i2sz 0, i2sz 0, params)

    prval () = pf_arr := pf_merged
    prval () = pf_work := array_v_unsplit (pf_cleared, pf_unused)
  in
  end

extern fn {a : vt@ype}
merge_right :
  {p_arr  : addr}
  {n      : pos}
  {i      : nat | i <= n; n <= 2 * i}
  {p_work : addr}
  {worksz : int | n - i <= worksz}
  (!array_v (a, p_arr, n),
   !array_v (a?, p_work, worksz) |
   bptr_anchor (a, p_arr),
   bptr (a, p_arr, i),
   bptr (a, p_arr, n),
   bptr_anchor (a?, p_work),
   &merge_params_vt >> _) -< !wrt >
    void

implement {a}
merge_right {p_arr} {n} {i} {p_work} {worksz}
            (pf_arr, pf_work | bp_arr, bp_i, bp_n, bp_work, params) =
  let
    stadef pntr (p : addr, i : int) = p + (i * sizeof a)

    (* Split the array into left and right, and copy the right to
       workspace. *)
    stadef p_temp = p_work
    stadef tempsz = n - i
    prval @(pf_left, pf_right) =
      array_v_split {a} {p_arr} {n} {i} pf_arr
    prval @(pf_temp, pf_unused) =
      array_v_split {a?} {p_work} {worksz} {tempsz} pf_work
    val () = copy<a> (pf_temp, pf_right |
                      bp_work, bptr_reanchor bp_i, bp_n - bp_i)
    val bp_temp : bptr_anchor (a, p_temp) =
      ptr2bptr_anchor (bptr2ptr bp_work)
    val bp_tempsz : bptr (a, p_temp, tempsz) =
      bp_temp + (bp_n - bp_i)

    fn {}
    right_is_done
              {i_lft      : nat | i_lft <= n}
              (pf_lft     : !array_v (a, p_arr, i_lft) >> void,
               pf_between : !array_v (a?, pntr (p_arr, i_lft), 0)
                              >> void,
               pf_merged  : !array_v (a, pntr (p_arr, i_lft),
                                      n - i_lft)
                              >> array_v (a, p_arr, n),
               pf_rgt     : !array_v (a, p_temp, 0) >> void | )
        :<!wrt> void =
      (* This routine generates no executable code, and could have
         been written as a prfn. *)
      let
        (* Any remaining left entries already are in place. *)
        prval () = pf_rgt := array_v_unnil pf_rgt
        prval () = pf_between := array_v_unnil pf_between
        prval () = pf_merged := array_v_unsplit (pf_lft,
                                                 pf_merged)
        prval () = pf_lft := ()
      in
      end

    fn
    left_is_done
              {i_rgt : nat | i_rgt <= n}
              (pf_lft     : !array_v (a, p_arr, 0) >> void,
               pf_between : !array_v (a?, p_arr, i_rgt) >> void,
               pf_merged  : !array_v (a, pntr (p_arr, i_rgt),
                                      n - i_rgt)
                              >> array_v (a, p_arr, n),
               pf_rgt     : !array_v (a, p_temp, i_rgt) >> void,
               pf_cleared : !array_v (a?!, pntr (p_temp, i_rgt),
                                      tempsz - i_rgt)
                              >> array_v (a?, p_temp, tempsz) |
               bp_rgt     : bptr (a, p_temp, i_rgt))
        :<!wrt> void =
      let                      (* Copy any remaining right entries. *)
        prval () = pf_lft := array_v_unnil pf_lft
        val () = copy<a> (pf_between, pf_rgt |
                          ptr2bptr_anchor (bptr2ptr bp_arr),
                          bp_temp, bp_rgt)
        prval () = pf_merged := array_v_unsplit (pf_between,
                                                 pf_merged)
        prval () = pf_between := ()
        prval () = pf_cleared := array_v_unsplit (pf_rgt,
                                                  pf_cleared)
        prval () = pf_rgt := ()
      in
      end

    fnx
    merge_runs
              {i_merged : nat | i_merged <= n}
              {i_lft    : nat | i_lft <= i_merged}
              {i_rgt    : nat | i_merged - i_lft == i_rgt}
              .<i_merged>.
              (pf_lft     : !array_v (a, p_arr, i_lft) >> void,
               pf_between : !array_v (a?, pntr (p_arr, i_lft),
                                      i_merged - i_lft) >> void,
               pf_merged  : !array_v (a, pntr (p_arr, i_merged),
                                      n - i_merged)
                              >> array_v (a, p_arr, n),
               pf_rgt     : !array_v (a, p_temp, i_rgt) >> void,
               pf_cleared : !array_v (a?!, pntr (p_temp, i_rgt),
                                      tempsz - i_rgt)
                              >> array_v (a?, p_temp, tempsz) |
               bp_merged  : bptr (a?, p_arr, i_merged),
               bp_lft     : bptr (a, p_arr, i_lft),
               bp_rgt     : bptr (a, p_temp, i_rgt),
               count_lft  : Size_t,
               count_rgt  : Size_t,
               params     : &merge_params_vt >> _)
        :<!wrt> void =
      if bp_rgt = bp_temp then
        let
          prval () = lemma_mul_isfun {i_lft, sizeof a}
                                     {i_merged, sizeof a} ()
          prval () = lemma_mul_isfun {i_rgt, sizeof a}
                                     {0, sizeof a} ()
        in
          right_is_done {i_lft}
                        (pf_lft, pf_between, pf_merged, pf_rgt | )
        end
      else if bp_lft = bp_arr then
        let
          prval () = lemma_mul_isfun {i_rgt, sizeof a}
                                     {i_merged, sizeof a} ()
          prval () = lemma_mul_isfun {i_lft, sizeof a}
                                     {0, sizeof a} ()
        in
          left_is_done {i_rgt}
                       (pf_lft, pf_between, pf_merged,
                        pf_rgt, pf_cleared |
                        bp_rgt)
        end
      else
        let
          prval @(pf_between1, pf_taken) = array_v_unextend pf_between
          prval @(pf_lft1, pf_L) = array_v_unextend pf_lft
          prval @(pf_rgt1, pf_R) = array_v_unextend pf_rgt
          val bp_merged = pred bp_merged
        in
          if elem_lt<a> (pf_R, pf_L | pred bp_rgt, pred bp_lft) then
            let                 (* L > R. Take L. *)
              prval () = pf_rgt := array_v_extend (pf_rgt1, pf_R)
              val bp_lft = pred bp_lft
              val x = bptr_get<a> (pf_L | bp_lft)
              val () = ptr_set<a> (pf_taken | bptr2ptr bp_merged, x)
              prval () = pf_merged := array_v_cons (pf_taken,
                                                    pf_merged)
              prval () = pf_lft := pf_lft1
              prval () = pf_between := array_v_cons (pf_L,
                                                     pf_between1)
              val count_lft = succ count_lft
              and count_rgt = i2sz 0
            in
              if count_lft >= (params.gallop_start_threshold) then
                galloping_merge (pf_lft, pf_between, pf_merged,
                                 pf_rgt, pf_cleared |
                                 bp_merged, bp_lft, bp_rgt, params)
              else
                merge_runs (pf_lft, pf_between, pf_merged,
                            pf_rgt, pf_cleared |
                            bp_merged, bp_lft, bp_rgt,
                            count_lft, count_rgt, params)
            end
          else
            let                 (* R >= L. Take R. *)
              prval () = pf_lft := array_v_extend (pf_lft1, pf_L)
              val bp_rgt = pred bp_rgt
              val x = bptr_get<a> (pf_R | bp_rgt)
              val () = ptr_set<a> (pf_taken | bptr2ptr bp_merged, x)
              prval () = pf_merged := array_v_cons (pf_taken,
                                                    pf_merged)
              prval () = pf_rgt := pf_rgt1
              prval () = pf_cleared := array_v_cons (pf_R, pf_cleared)
              prval () = pf_between := pf_between1
              val count_lft = i2sz 0
              and count_rgt = succ count_rgt
            in
              if count_rgt >= (params.gallop_start_threshold) then
                galloping_merge (pf_lft, pf_between, pf_merged,
                                 pf_rgt, pf_cleared |
                                 bp_merged, bp_lft, bp_rgt, params)
              else
                merge_runs (pf_lft, pf_between, pf_merged,
                            pf_rgt, pf_cleared |
                            bp_merged, bp_lft, bp_rgt,
                            count_lft, count_rgt, params)
            end
        end
    and
    galloping_merge
              {i_merged : nat | i_merged <= n}
              {i_lft    : nat | i_lft <= i_merged}
              {i_rgt    : nat | i_merged - i_lft == i_rgt}
              .<i_merged>.
              (pf_lft     : !array_v (a, p_arr, i_lft) >> void,
               pf_between : !array_v (a?, pntr (p_arr, i_lft),
                                      i_merged - i_lft) >> void,
               pf_merged  : !array_v (a, pntr (p_arr, i_merged),
                                      n - i_merged)
                              >> array_v (a, p_arr, n),
               pf_rgt     : !array_v (a, p_temp, i_rgt) >> void,
               pf_cleared : !array_v (a?!, pntr (p_temp, i_rgt),
                                      tempsz - i_rgt)
                              >> array_v (a?, p_temp, tempsz) |
               bp_merged  : bptr (a?, p_arr, i_merged),
               bp_lft     : bptr (a, p_arr, i_lft),
               bp_rgt     : bptr (a, p_temp, i_rgt),
               params     : &merge_params_vt >> _)
        :<!wrt> void =
      if bp_rgt = bp_temp then
        let
          prval () = lemma_mul_isfun {i_lft, sizeof a}
                                     {i_merged, sizeof a} ()
          prval () = lemma_mul_isfun {i_rgt, sizeof a}
                                     {0, sizeof a} ()
        in
          right_is_done {i_lft}
                        (pf_lft, pf_between, pf_merged, pf_rgt | )
        end
      else if bp_lft = bp_arr then
        let
          prval () = lemma_mul_isfun {i_rgt, sizeof a}
                                     {i_merged, sizeof a} ()
          prval () = lemma_mul_isfun {i_lft, sizeof a}
                                     {0, sizeof a} ()
        in
          left_is_done {i_rgt}
                       (pf_lft, pf_between, pf_merged,
                        pf_rgt, pf_cleared |
                        bp_rgt)
        end
      else
        let
          prval () = prop_verify {i_lft < n} ()

          (* Find a position within the right side data. *)
          val [count_rgt0 : int] bp =
            find_1st_position_past_lt_x
              {p_temp} {i_rgt} {i_rgt - 1}
              {p_arr} {i_lft} {i_lft - 1}
              (pf_rgt, pf_lft | bp_temp, bp_rgt,
                                pred bp_rgt - bp_temp,
                                pred bp_lft)
          stadef count_rgt = i_rgt - count_rgt0

          (* This is how much to copy. *)
          val count_rgt : size_t count_rgt = bp_rgt - bp

          (* Copy the data. *)
          prval @(pf_between1, pf_between2) =
            array_v_split {a?} {pntr (p_arr, i_lft)}
                          {i_merged - i_lft}
                          {i_merged - i_lft - count_rgt}
                          pf_between
          prval @(pf_rgt1, pf_rgt2) =
            array_v_split {a} {p_temp} {i_rgt} {i_rgt - count_rgt}
                          pf_rgt
          stadef i_merged = i_merged - count_rgt
          stadef i_rgt = i_rgt - count_rgt
          val bp_merged = bp_merged - count_rgt
          and bp_rgt = bp_rgt - count_rgt
          val () = copy<a> (pf_between2, pf_rgt2 |
                            bptr_reanchor bp_merged,
                            bptr_reanchor bp, count_rgt)
          prval () = pf_merged :=
            array_v_unsplit (pf_between2, pf_merged)
          prval () = pf_between := pf_between1
          prval () = pf_cleared :=
            array_v_unsplit (pf_rgt2, pf_cleared)
          prval () = pf_rgt := pf_rgt1
        in
          if bp_rgt = bp_temp then
            let
              prval () = lemma_mul_isfun {i_lft, sizeof a}
                                         {i_merged, sizeof a} ()
              prval () = lemma_mul_isfun {i_rgt, sizeof a}
                                         {0, sizeof a} ()
            in
              if ((succ (bp_lft - bp_arr))
                      >= (params.gallop_stop_threshold))
                    + (count_rgt
                          >= (params.gallop_stop_threshold)) then
                lower_gallop_thresholds params
              else
                raise_gallop_thresholds params;

              right_is_done {i_lft}
                            (pf_lft, pf_between, pf_merged, pf_rgt | )
            end
          else
            let
              (* Copy the left side element whose position has been
                 found. *)
              prval @(pf_between1, pf_taken) =
                array_v_unextend pf_between
              prval @(pf_lft1, pf_L) = array_v_unextend pf_lft
              stadef i_lft = i_lft - 1
              stadef i_merged = i_merged - 1
              val bp_lft = pred bp_lft
              and bp_merged = pred bp_merged
              val x = bptr_get<a> (pf_L | bp_lft)
              val () = ptr_set<a> (pf_taken | bptr2ptr bp_merged, x)
              prval () = pf_merged :=
                array_v_cons (pf_taken, pf_merged)
              and () = pf_between :=
                array_v_cons (pf_L, pf_between1)
              and () = pf_lft := pf_lft1
            in
              if bp_lft = bp_arr then
                let
                  prval () = lemma_mul_isfun {i_rgt, sizeof a}
                                             {i_merged, sizeof a} ()
                  prval () = lemma_mul_isfun {i_lft, sizeof a}
                                             {0, sizeof a} ()
                in
                  if count_rgt >= (params.gallop_stop_threshold) then
                    lower_gallop_thresholds params
                  else
                    raise_gallop_thresholds params;

                  left_is_done {i_rgt}
                               (pf_lft, pf_between, pf_merged,
                                pf_rgt, pf_cleared |
                                bp_rgt)
                end
              else
                let
                  (* Find a position within the left side data. *)
                  val [count_lft0 : int] bp =
                    find_1st_position_past_lte_x
                      {p_arr} {i_lft} {i_lft - 1}
                      {p_temp} {i_rgt} {i_rgt - 1}
                      (pf_lft, pf_rgt | bp_arr, bp_lft,
                                        pred (bp_lft - bp_arr),
                                        pred bp_rgt)
                  stadef count_lft = i_lft - count_lft0

                  (* This is how much to copy. *)
                  val count_lft : size_t count_lft = bp_lft - bp

                  (* Copy the data. *)
                  prval @(pf_lft1, pf_lft2) =
                    array_v_split {a} {p_arr} {i_lft}
                                  {i_lft - count_lft}
                                  pf_lft
                  stadef i_lft = i_lft - count_lft
                  stadef i_merged = i_merged - count_lft
                  val bp_lft = bp_lft - count_lft
                  and bp_merged = bp_merged - count_lft
                  val bp0 = bptr_reanchor bp_lft
                  val bp1 = ptr2bptr_anchor (bptr2ptr bp0)
                                + (bp_merged - bp_lft)
                  val () =
                    move_right<a> {pntr (p_arr, i_lft)}
                                  {i_merged - i_lft} {count_lft}
                                  (pf_between, pf_lft2 |
                                   bp1, bp0, count_lft)
                  prval () = pf_merged :=
                    array_v_unsplit (pf_between, pf_merged)
                  and () = pf_between := pf_lft2
                  and () = pf_lft := pf_lft1

                  (* Copy the right side element whose position has
                     been found. *)
                  prval @(pf_between1, pf_taken) =
                    array_v_unextend pf_between
                  prval @(pf_rgt1, pf_R) = array_v_unextend pf_rgt
                  stadef i_rgt = i_rgt - 1
                  stadef i_merged = i_merged - 1
                  val bp_rgt = pred bp_rgt
                  and bp_merged = pred bp_merged
                  val x = bptr_get<a> (pf_R | bp_rgt)
                  val () = ptr_set<a> (pf_taken |
                                       bptr2ptr bp_merged, x)
                  prval () = pf_merged :=
                    array_v_cons (pf_taken, pf_merged)
                  and () = pf_between := pf_between1
                  and () = pf_cleared :=
                    array_v_cons (pf_R, pf_cleared)
                  and () = pf_rgt := pf_rgt1
                in
                  if (count_lft >= (params.gallop_stop_threshold))
                        + (count_rgt
                              >= (params.gallop_stop_threshold)) then
                    begin
                      (* Lower the gallop threshold and continue
                         galloping. *)
                      lower_gallop_thresholds params;
                      galloping_merge (pf_lft, pf_between, pf_merged,
                                       pf_rgt, pf_cleared |
                                       bp_merged, bp_lft, bp_rgt,
                                       params)
                    end
                  else
                    begin
                      (* Raise the gallop threshold and stop galloping. *)
                      raise_gallop_thresholds params;
                      merge_runs (pf_lft, pf_between, pf_merged,
                                  pf_rgt, pf_cleared |
                                  bp_merged, bp_lft, bp_rgt,
                                  i2sz 0, i2sz 0, params)
                    end
                end
            end
        end

    prval pf_merged = array_v_nil {a} {pntr (p_arr, n)} ()
    prval pf_between = pf_right
    prval pf_cleared = array_v_nil {a?!} {pntr (p_temp, tempsz)} ()
    val () = merge_runs (pf_left, pf_between, pf_merged,
                         pf_temp, pf_cleared |
                         ptr2bptr_anchor (bptr2ptr bp_arr)
                            + (bp_n - bp_arr),
                         bp_i, bp_tempsz, i2sz 0, i2sz 0, params)

    prval () = pf_arr := pf_merged
    prval () = pf_work := array_v_unsplit (pf_cleared, pf_unused)
  in
  end

extern fn {a : vt@ype}
merge_adjacent_runs :
  {p_arr  : addr}
  {n      : int}
  {i      : nat | 1 <= i; i <= n - 1}
  {p_work : addr}
  {worksz : int | min (i, n - i) <= worksz}
  (!array_v (a, p_arr, n),
   !array_v (a?, p_work, worksz) |
   bptr_anchor (a, p_arr),
   bptr (a, p_arr, i),
   bptr (a, p_arr, n),
   bptr_anchor (a?, p_work),
   &merge_params_vt >> _) -< !wrt >
    void

implement {a}
merge_adjacent_runs {p_arr} {n} {i} {p_work} {worksz}
                    (pf_arr, pf_work |
                     bp_arr, bp_i, bp_n, bp_work, params) =
  let
    (* Find any prefix that already is in place. *)
    prval @(pf_lft, pf_rgt) =
      array_v_split {a} {p_arr} {n} {i} pf_arr
    val [n_pfx : int] bp_past_prefix =
      find_1st_position_past_lte_x
        (pf_lft, pf_rgt | bp_arr, bp_i, i2sz 0, bptr_reanchor bp_i)
    prval () = pf_arr := array_v_unsplit (pf_lft, pf_rgt)
  in
    if bp_past_prefix = bp_i then
      ()                        (* The array is already sorted. *)
    else
      let
        (* Find any suffix that already is in place. *)
        prval @(pf_lft, pf_rgt) =
          array_v_split {a} {p_arr} {n} {i} pf_arr
        val bp_i0 = bptr_reanchor bp_i
        val bp_n0 = bp_i0 + (bp_n - bp_i)
        val [n_sfx0 : int] bp_at_suffix =
          find_1st_position_past_lt_x
            (pf_rgt, pf_lft | bp_i0, bp_n0, pred (bp_n0 - bp_i0),
                              pred bp_i)
        stadef n_sfx = n - i - n_sfx0
        prval () = pf_arr := array_v_unsplit (pf_lft, pf_rgt)

        prval @(pf_prefix, pf_arr1) =
          array_v_split {a} {p_arr} {n} {n_pfx} pf_arr
        prval @(pf_middle, pf_suffix) =
          array_v_split {a} {p_arr + (n_pfx * sizeof a)}
                        {n - n_pfx} {n - n_pfx - n_sfx}
                        pf_arr1

        val bp0 = bptr_reanchor bp_past_prefix
        val bp1 = bp0 + (bp_i - bp_past_prefix)
        val bp2 = bp1 + (bp_at_suffix - bp_i0)

        val () =
          begin
            if bp1 - bp0 <= bp2 - bp1 then
              merge_left (pf_middle, pf_work |
                          bp0, bp1, bp2, bp_work, params)
            else
              merge_right (pf_middle, pf_work |
                           bp0, bp1, bp2, bp_work, params)
          end

        prval () = pf_arr1 := array_v_unsplit (pf_middle, pf_suffix)
        prval () = pf_arr := array_v_unsplit (pf_prefix, pf_arr1)
      in
      end
  end

(*------------------------------------------------------------------*)
(* Powersort strategy.                                              *)

extern fn {a : vt@ype}
include_new_run
          {p_arr   : addr}
          {n       : int}
          {index   : nat}
          {size    : pos | index + size <= n}
          {p_work  : addr}
          {worksz  : int | n <= 2 * worksz}
          {p_stk   : addr}
          {stk_max : int}
          {depth0  : nat | depth0 <= stk_max - 1}
          (pf_arr  : !array_v (a, p_arr, n),
           pf_work : !array_v (a?, p_work, worksz) |
           p_arr   : ptr p_arr,
           n       : size_t n,
           index   : size_t index,
           size    : size_t size,
           p_work  : ptr p_work,
           params  : &merge_params_vt >> _,
           stk     : &stk_vt (p_stk, depth0, stk_max)
                      >> stk_vt (p_stk, depth1, stk_max))
    :<!wrt> #[depth1 : pos | depth1 <= depth0 + 1]
            void

#define ARBITRARY_POWER ~1234

implement {a}
include_new_run {p_arr} {n} {index} {size} {p_work} {worksz}
                (pf_arr, pf_work | p_arr, n, index, size,
                                   p_work, params, stk) =
  if stk_vt_depth stk = 0 then
    stk_vt_push (index, size, ARBITRARY_POWER, stk)
  else
    let
      val @{
            index = index0,
            size = size0,
            power = _
          } = stk_vt_peek (stk, 0)

      prval [index0 : int] EQINT () = eqint_make_guint index0
      prval [size0 : int] EQINT () = eqint_make_guint size0

      val () = $effmask_exn assertloc (index0 + size0 = index)
      prval () = prop_verify {index0 + size0 + size <= n} ()

      val power = nodepower (n, index0, size0, size)

      fun
      merge_subarrays
                {p_stk   : addr}
                {stk_max : int}
                {depth1  : pos | depth1 <= stk_max - 1}
                .<depth1>.
                (pf_arr  : !array_v (a, p_arr, n),
                 pf_work : !array_v (a?, p_work, worksz) |
                 params  : &merge_params_vt >> _,
                 stk     : &stk_vt (p_stk, depth1, stk_max)
                            >> stk_vt (p_stk, depth2, stk_max))
          :<!wrt> #[depth2 : pos | depth2 <= depth1]
                  void =
        if stk_vt_depth stk = 1 then
          ()
        else if ((stk_vt_peek (stk, 1)).power) <= power then
          ()
        else
          let
            val @{
                  index = index0,
                  size = size0,
                  power = _
                } = stk_vt_peek (stk, 0)
            and @{
                  index = index1,
                  size = size1,
                  power = _
                } = stk_vt_peek (stk, 1)

            prval [index0 : int] EQINT () = eqint_make_guint index0
            prval [size0 : int] EQINT () = eqint_make_guint size0
            prval [index1 : int] EQINT () = eqint_make_guint index1
            prval [size1 : int] EQINT () = eqint_make_guint size1

            val () = $effmask_exn assertloc (index1 + size1 = index0)
            val () = $effmask_exn assertloc (index0 + size0 = index)
            prval () =
              prop_verify {index1 + size1 + size0 + size <= n} ()

            prval @(pf_before, pf_arr1) =
              array_v_split {a} {p_arr} {n} {index1} pf_arr
            prval @(pf_middle, pf_after) =
              array_v_split {a} {p_arr + (index1 * sizeof a)}
                            {n - index1} {size1 + size0}
                            pf_arr1

            val bp_arr : bptr_anchor (a, p_arr) =
              ptr2bptr_anchor p_arr
            and bp_work : bptr_anchor (a?, p_work) =
              ptr2bptr_anchor p_work

            val bp_middle = bptr_reanchor (bp_arr + index1)
            val bp_middle_i = bp_middle + size1
            val bp_middle_n = bp_middle_i + size0

            val () =
              merge_adjacent_runs<a>
                {p_arr + (index1 * sizeof a)}
                {size1 + size0} {size1} {p_work} {worksz}
                (pf_middle, pf_work |
                 bp_middle, bp_middle_i, bp_middle_n, bp_work, params)

            prval () = pf_arr1 :=
              array_v_unsplit (pf_middle, pf_after)
            prval () = pf_arr :=
              array_v_unsplit (pf_before, pf_arr1)
          in
            stk_vt_overwrite (index1, size1 + size0, ARBITRARY_POWER,
                              stk, 1);
            stk_vt_drop stk;
            merge_subarrays (pf_arr, pf_work | params, stk)
          end
    in
      merge_subarrays (pf_arr, pf_work | params, stk);
      stk_vt_overwrite ((stk_vt_peek (stk, 0)).index,
                        (stk_vt_peek (stk, 0)).size,
                        power, stk, 0);
      stk_vt_push (index, size, ARBITRARY_POWER, stk)
    end

extern fn {a : vt@ype}
merge_remaining_runs
          {p_arr   : addr}
          {n       : int}
          {p_work  : addr}
          {worksz  : int | n <= 2 * worksz}
          {p_stk   : addr}
          {stk_max : int}
          {depth0  : pos | depth0 <= stk_max}
          (pf_arr  : !array_v (a, p_arr, n),
           pf_work : !array_v (a?, p_work, worksz) |
           p_arr   : ptr p_arr,
           n       : size_t n,
           p_work  : ptr p_work,
           params  : &merge_params_vt >> _,
           stk     : &stk_vt (p_stk, depth0, stk_max)
                      >> stk_vt (p_stk, 0, stk_max))
    :<!wrt> void

implement {a}
merge_remaining_runs {p_arr} {n} {p_work} {worksz}
                     (pf_arr, pf_work | p_arr, n, p_work,
                                        params, stk) =
  let
    fn
    merge_1_with_0
              {p_stk   : addr}
              {stk_max : int}
              {depth   : int | 2 <= depth; depth <= stk_max}
              (pf_arr  : !array_v (a, p_arr, n),
               pf_work : !array_v (a?, p_work, worksz) |
               params  : &merge_params_vt >> _,
               stk     : &stk_vt (p_stk, depth, stk_max)
                          >> stk_vt (p_stk, depth - 1, stk_max))
        :<!wrt> void =
      let
        val @{
              index = index0,
              size = size0,
              power = _
            } = stk_vt_pop stk
        val @{
              index = index1,
              size = size1,
              power = _
            } = stk_vt_peek (stk, 0)

        prval [index1 : int] EQINT () = eqint_make_guint index1
        prval [size1 : int] EQINT () = eqint_make_guint size1
        prval [index0 : int] EQINT () = eqint_make_guint index0
        prval [size0 : int] EQINT () = eqint_make_guint size0

        val () = $effmask_exn assertloc (index1 + size1 = index0)
        val () = $effmask_exn assertloc (index0 + size0 = n)

        prval @(pf_before, pf_arr1) =
          array_v_split {a} {p_arr} {n} {index1} pf_arr
        prval @(pf_middle, pf_after) =
          array_v_split {a} {p_arr + (index1 * sizeof a)}
                        {n - index1} {size1 + size0}
                        pf_arr1

        val bp_arr = ptr2bptr_anchor p_arr
        and bp_work = ptr2bptr_anchor p_work

        val bp_middle = bptr_reanchor (bp_arr + index1)
        val bp_middle_i = bp_middle + size1
        val bp_middle_n = bp_middle_i + size0

        val () =
          merge_adjacent_runs<a>
            {p_arr + (index1 * sizeof a)}
            {size1 + size0} {size1} {p_work} {worksz}
            (pf_middle, pf_work |
             bp_middle, bp_middle_i, bp_middle_n, bp_work, params)

        prval () = pf_arr1 :=
          array_v_unsplit (pf_middle, pf_after)
        prval () = pf_arr :=
          array_v_unsplit (pf_before, pf_arr1)
      in
        stk_vt_overwrite (index1, size1 + size0, ARBITRARY_POWER,
                          stk, 0)
      end

    fn
    merge_2_with_1
              {p_stk   : addr}
              {stk_max : int}
              {depth   : int | 3 <= depth; depth <= stk_max}
              (pf_arr  : !array_v (a, p_arr, n),
               pf_work : !array_v (a?, p_work, worksz) |
               params  : &merge_params_vt >> _,
               stk     : &stk_vt (p_stk, depth, stk_max)
                          >> stk_vt (p_stk, depth - 1, stk_max))
        :<!wrt> void =
      let
        val @{
              index = index0,
              size = size0,
              power = _
            } = stk_vt_pop stk
        val @{
              index = index1,
              size = size1,
              power = _
            } = stk_vt_pop stk
        val @{
              index = index2,
              size = size2,
              power = _
            } = stk_vt_pop stk

        prval [index2 : int] EQINT () = eqint_make_guint index2
        prval [size2 : int] EQINT () = eqint_make_guint size2
        prval [index1 : int] EQINT () = eqint_make_guint index1
        prval [size1 : int] EQINT () = eqint_make_guint size1
        prval [index0 : int] EQINT () = eqint_make_guint index0
        prval [size0 : int] EQINT () = eqint_make_guint size0

        val () = $effmask_exn assertloc (index2 + size2 = index1)
        val () = $effmask_exn assertloc (index1 + size1 = index0)
        val () = $effmask_exn assertloc (index0 + size0 = n)

        prval @(pf_before, pf_arr1) =
          array_v_split {a} {p_arr} {n} {index2} pf_arr
        prval @(pf_middle, pf_after) =
          array_v_split {a} {p_arr + (index2 * sizeof a)}
                        {n - index2} {size2 + size1}
                        pf_arr1

        val bp_arr = ptr2bptr_anchor p_arr
        and bp_work = ptr2bptr_anchor p_work

        val bp_middle = bptr_reanchor (bp_arr + index2)
        val bp_middle_i = bp_middle + size2
        val bp_middle_n = bp_middle_i + size1

        val () =
          merge_adjacent_runs<a>
            {p_arr + (index2 * sizeof a)}
            {size2 + size1} {size2} {p_work} {worksz}
            (pf_middle, pf_work |
             bp_middle, bp_middle_i, bp_middle_n, bp_work, params)

        prval () = pf_arr1 :=
          array_v_unsplit (pf_middle, pf_after)
        prval () = pf_arr :=
          array_v_unsplit (pf_before, pf_arr1)
      in
        stk_vt_push (index2, size2 + size1, ARBITRARY_POWER, stk);
        stk_vt_push (index0, size0, ARBITRARY_POWER, stk)
      end

    fun
    loop {p_stk   : addr}
         {stk_max : int}
         {depth   : pos | depth <= stk_max}
         .<depth>.
         (pf_arr  : !array_v (a, p_arr, n),
          pf_work : !array_v (a?, p_work, worksz) |
          params  : &merge_params_vt >> _,
          stk     : &stk_vt (p_stk, depth, stk_max)
                     >> stk_vt (p_stk, 0, stk_max))
        :<!wrt> void =
      if stk_vt_depth stk = 1 then
        stk_vt_drop stk
      else if stk_vt_depth stk = 2 then
        begin
          merge_1_with_0 (pf_arr, pf_work | params, stk);
          loop (pf_arr, pf_work | params, stk)
        end
      else if ((stk_vt_peek (stk, 0)).size)
                  <= ((stk_vt_peek (stk, 2)).size) then
        begin
          merge_1_with_0 (pf_arr, pf_work | params, stk);
          loop (pf_arr, pf_work | params, stk)
        end
      else
        begin
          merge_2_with_1 (pf_arr, pf_work | params, stk);
          loop (pf_arr, pf_work | params, stk)
        end
  in
    loop (pf_arr, pf_work | params, stk)
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
  let
    prval () = lemma_array_v_param pf_arr

    val minrun = minimum_run_length n
    and bp_arr = ptr2bptr_anchor p_arr
    val bp_n = bp_arr + n

    fun
    loop {i      : nat | i <= n}
         {depth0 : nat | depth0 <= stk_max;
                         i == n || depth0 < stk_max}
         .<n - i>.
         (pf_arr  : !array_v (a, p_arr, n),
          pf_work : !array_v (a?, p_work, worksz) |
          i       : size_t i,
          params  : &merge_params_vt >> _,
          stk     : &stk_vt (p_stk, depth0, stk_max)
                     >> stk_vt (p_stk, depth1, stk_max))
        :<!wrt> #[depth1 : pos | depth1 <= stk_max]
                void =
      if i = n then
        $effmask_exn assertloc (0 < stk_vt_depth stk)
      else
        let
          val bp_i = bp_arr + i
          val bp_j =
            provide_a_sorted_run<a> (pf_arr | bp_i, bp_n, minrun)
          val j = bp_j - bp_arr
        in
          include_new_run (pf_arr, pf_work |
                           p_arr, n, i, j - i, p_work,
                           params, stk);
          let
            val () = $effmask_exn
              assertloc
                ((j = n) +
                  (i2sz (stk_vt_depth stk) < stk_vt_stk_max stk));
          in
            loop (pf_arr, pf_work | j, params, stk)
          end
        end

    var params : merge_params_vt
    val () = initialize_gallop_thresholds params
  in
    loop (pf_arr, pf_work | i2sz 0, params, stk);
    merge_remaining_runs<a> (pf_arr, pf_work |
                             p_arr, n, p_work, params, stk)
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
          @[stk_entry_t][STK_MAX_THRESHOLD]
            (@{
               index = i2sz 0,
               size = i2sz 0,
               power = 0
             })
        var stk = stk_vt_make (view@ stk_storage |
                               addr@ stk_storage,
                               i2sz STK_MAX_THRESHOLD)
        val () = sort_main (pf_arr, pf_work | p_arr, n, p_work, stk)
        prval () = view@ stk_storage := stk.pf
      in
      end
    else
      let                       (* Put stk in the heap. *)
        val bitsz = char_bit () * sizeof<size_t>
        val () = $effmask_exn assertloc (i2sz 1 <= bitsz)
        val @(pf_stk_storage, pfgc_stk_storage | p_stk_storage) =
          array_ptr_alloc<stk_entry_t> bitsz
        val entry =
          @{
            index = i2sz 0,
            size = i2sz 0,
            power = 0
          }
        val () = array_initize_elt<stk_entry_t> (!p_stk_storage,
                                                 bitsz, entry)
        var stk = stk_vt_make (pf_stk_storage | p_stk_storage, bitsz)
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

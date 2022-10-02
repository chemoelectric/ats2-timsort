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

staload "timsort/SATS/list-timsort.sats"

staload "timsort/SATS/COMMON/timsort-common.sats"
staload _ = "timsort/DATS/COMMON/timsort-common.dats"

#define STK_MAX_THRESHOLD 64   (* The bitsize of a size_t on AMD64. *)

#define NIL list_vt_nil ()
#define ::  list_vt_cons

macdef orelse1 (a, b) = (if ,(a) then true else ,(b))
infix ( || ) |||
macdef ||| = orelse1

macdef andalso1 (a, b) = (if ,(a) then ,(b) else false)
infix ( && ) &&&
macdef &&& = andalso1

(*------------------------------------------------------------------*)

implement {a}
list_vt_timsort$lt (x, y) =
  list_vt_timsort$cmp<a> (x, y) < 0

implement {a}
list_vt_timsort$cmp (x, y) =
  (* This default is the same as for list_vt_mergesort$cmp in the
     prelude. *)
  gcompare_ref_ref<a> (x, y)

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
list_vt_insertion_sort_with_some_of_it_presorted :
  {m, n : int}
  (list_vt (a, m),
   list_vt (a, n)) -< !wrt >
    list_vt (a, m + n)

extern fn {a : vt@ype}
list_vt_insertion_sort_without_any_of_it_presorted :
  {n : int}
  list_vt (a, n) -< !wrt >
    list_vt (a, n)

extern fn {a : vt@ype}
list_vt_insertion_sort$lt :
  (&a, &a) -<> bool

overload list_vt_insertion_sort with
  list_vt_insertion_sort_with_some_of_it_presorted
overload list_vt_insertion_sort with
  list_vt_insertion_sort_without_any_of_it_presorted

implement {a}
list_vt_insertion_sort_with_some_of_it_presorted
                    {m, n} (lst, presorted) =
  let
    prval () = lemma_list_vt_param lst
    prval () = lemma_list_vt_param presorted

    fun
    insert {u       : nat}
           {p_xnode : addr}
           {p_x     : addr}
           {p_xs    : addr}
           .<u>.
           (pf_x  : a @ p_x,
            pf_xs : list_vt (a, 0)? @ p_xs |
            dst   : &list_vt (a, u) >> list_vt (a, u + 1),
            (* list_vt_cons_unfold is a viewtype created by the
               unfolding of a list_vt_cons (our :: operator). *)
            xnode : list_vt_cons_unfold (p_xnode, p_x, p_xs),
            p_x   : ptr p_x,
            p_xs  : ptr p_xs)
        :<!wrt> void =

      (*
        dst is some tail of the current destination list; xnode is a
        viewtype for the current node in the source list.

        p_x points to the node's CAR.

        p_xs points to the node's CDR.
      *)
      case+ dst of
      | @ (y :: ys) =>
        if ~list_vt_insertion_sort$lt<a> (!p_x, y) then
          let                 (* Move to the next destination node. *)
            val () = insert (pf_x, pf_xs | ys, xnode, p_x, p_xs)
            prval () = fold@ dst
          in
          end
        else
          let                   (* Insert xnode here. *)
            prval () = fold@ dst
            val () = !p_xs := dst
            val () = dst := xnode
            prval () = fold@ dst
          in
          end
      | ~ NIL =>
        let                     (* Put xnode at the end. *)
          val () = dst := xnode
          val () = !p_xs := NIL
          prval () = fold@ dst
        in
        end

    fun                         (* Create a sorted list. *)
    loop {u : int | n <= u; u <= n + m}
         .<n + m - u>.
         (dst : &list_vt (a, u) >> list_vt (a, n + m),
          src : list_vt (a, n + m - u))
        :<!wrt> void =
      case+ src of
      | @ (x :: xs) =>
        let
          val tail = xs
        in
          insert (view@ x, view@ xs | dst, src, addr@ x, addr@ xs);
          loop (dst, tail)
        end
      | ~ NIL => ()             (* We are done. *)

    var dst : [u : int | n <= u] list_vt (a, u) = presorted
  in
    loop (dst, lst);
    dst
  end

implement {a}
list_vt_insertion_sort_without_any_of_it_presorted lst =
  list_vt_insertion_sort_with_some_of_it_presorted<a> (lst, NIL)

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
split_at_pair_after_first :
  {n : int | 2 <= n}
  list_vt (a, n) -< !wrt >
    [m : int | 2 <= m; m <= n]
    @(list_vt (a, m),
      list_vt (a, n - m))

extern fn {a : vt@ype}
split_at_pair_after_first$here :
  (&a, &a) -<> bool

implement {a}
split_at_pair_after_first {n} lst =
  let
    fun
    loop {u : nat | u + 2 <= n}
         .<u>.
         (lst1a : &list_vt (a, u) >> list_vt (a, v),
          lst2  : &(List_vt a)? >> list_vt (a, u - v),
          prev  : &a)
        :<!wrt> #[v : nat | v <= u]
                void =
      case+ lst1a of
      | NIL => lst2 := NIL
      | @ (next :: rest) =>
        let
          val done = split_at_pair_after_first$here<a> (prev, next)
        in
          if done then
            let
              prval () = fold@ lst1a
            in
              lst2 := lst1a;
              lst1a := NIL
            end
          else
            let
              val () = loop (rest, lst2, next)
              prval () = fold@ lst1a
            in
            end
        end

    var lst1 = lst
    var lst2 : List_vt a?

    (* It is assumed that the second list element is not less than the
       first. (We do not prove the result is monotonically
       non-descending, anyway, so I will not bother to prove or assert
       this precondition. We will unit-test the routine.) *)

    val+ @ (_first :: rest1) = lst1
    val+ @ (second :: rest2) = rest1
    val () = loop (rest2, lst2, second)
    prval () = fold@ rest1
    prval () = fold@ lst1
  in
    @(lst1, lst2)
  end

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
split_after_nondecreasing_run :
  {n : int | 2 <= n}
  list_vt (a, n) -< !wrt >
    [m : int | 2 <= m; m <= n]
    @(list_vt (a, m),
      list_vt (a, n - m))

implement {a}
split_after_nondecreasing_run {n} lst =
  let
    implement
    split_at_pair_after_first$here<a> (prev, next) =
      list_vt_timsort$lt<a> (next, prev)
  in
    split_at_pair_after_first {n} lst
  end

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
split_after_decreasing_run :
  {n : int | 2 <= n}
  list_vt (a, n) -< !wrt >
    [m : int | 2 <= m; m <= n]
    @(list_vt (a, m),
      list_vt (a, n - m))

implement {a}
split_after_decreasing_run {n} lst =
  let
    implement
    split_at_pair_after_first$here<a> (prev, next) =
      ~list_vt_timsort$lt<a> (next, prev)
  in
    split_at_pair_after_first {n} lst
  end

(*------------------------------------------------------------------*)

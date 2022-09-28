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
list_vt_insertion_sort :
  {n : int}
  list_vt (a, n) -< !wrt > list_vt (a, n)

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
list_vt_insertion_sort_reverse :
  {n : int}
  list_vt (a, n) -< !wrt > list_vt (a, n)

implement {a}
list_vt_insertion_sort_reverse {n} lst =
  let
    fun
    insert_reverse
              {m       : nat}
              {p_xnode : addr}
              {p_x     : addr}
              {p_xs    : addr}
              .<m>.
              (pf_x  : a @ p_x,
               pf_xs : list_vt (a, 0)? @ p_xs |
               dst   : &list_vt (a, m) >> list_vt (a, m + 1),
               (* list_vt_cons_unfold is a viewtype created by the
                  unfolding of a list_vt_cons (our :: operator). *)
               xnode : list_vt_cons_unfold (p_xnode, p_x, p_xs),
               p_x   : ptr p_x,
               p_xs  : ptr p_xs)
        :<!wrt> void =
      (* dst is some tail of the current (reverse-order) destination
         list.  xnode is a viewtype for the current node in the source
         list.
         p_x points to the node's CAR.
         p_xs points to the node's CDR. *)
      case+ dst of
      | @ (y :: ys) =>
        if list_vt_timsort$lt<a> (!p_x, y) then
          let                 (* Move to the next destination node. *)
            val () = insert_reverse (pf_x, pf_xs |
                                     ys, xnode, p_x, p_xs)
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

    fun                         (* Create a list sorted in reverse. *)
    loop {i : nat | i <= n}
         .<n - i>.
         (dst : &list_vt (a, i) >> list_vt (a, n),
          src : list_vt (a, n - i))
        :<!wrt> void =
      case+ src of
      | @ (x :: xs) =>
        let
          val tail = xs
        in
          insert_reverse (view@ x, view@ xs |
                          dst, src, addr@ x, addr@ xs);
          loop (dst, tail)
        end
      | ~ NIL => ()             (* We are done. *)

    prval () = lemma_list_vt_param lst

    var dst : List_vt a = NIL
  in
    loop (dst, lst);
    dst
  end

(*------------------------------------------------------------------*)

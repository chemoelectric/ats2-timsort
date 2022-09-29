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

(* Unit testing of the list insertion sort. *)

#include "share/atspre_staload.hats"
staload UN = "prelude/SATS/unsafe.sats"

#include "timsort/DATS/list-timsort.dats"

#define NIL list_nil ()
#define ::  list_cons

(*------------------------------------------------------------------*)

typedef entry_t =
  @(int, int)

implement
list_equal$eqfn<entry_t> (x, y) =
  ((x.0) = (y.0)) * ((x.1) = (y.1))

fn
display {n   : int}
        (lst : list (entry_t, n))
    : void =
  let
    fun
    loop {n : nat}
         .<n>.
         (lst : list (entry_t, n))
        : void =
      case+ lst of
      | NIL => ()
      | head :: tail =>
        begin
          print! (" (", head.0, " ", head.1, ")");
          loop tail
        end

    prval () = lemma_list_param lst
  in
    loop lst;
    println! ()
  end

fn
test_list {n   : int}
          (lst : list (entry_t, n))
    : void =
  let
    implement
    list_vt_mergesort$cmp<entry_t> (x, y) =
      if (x.0) < (y.0) then
        ~1
      else if (x.0) > (y.0) then
        1
      else
        0

    implement
    list_vt_insertion_sort$lt<entry_t> (x, y) =
      (x.0) < (y.0)

    macdef cpy = list_copy<entry_t>
    val expected = list_vt2t (list_vt_mergesort<entry_t> (cpy lst))
    val gotten = list_vt2t (list_vt_insertion_sort<entry_t> (cpy lst))
  in
    display expected;
    display gotten;
    assertloc (gotten = expected)
  end

fn
test_list_reverse_order
          {n   : int}
          (lst : list (entry_t, n))
    : void =
  let
    implement
    list_vt_mergesort$cmp<entry_t> (x, y) =
      if (x.0) < (y.0) then
        ~1
      else if (x.0) > (y.0) then
        1
      else
        0

    implement
    list_vt_insertion_sort$lt<entry_t> (x, y) =
      (* Use >= instead of >, to reverse the ‘order of stability’. *)
      (x.0) >= (y.0)

    macdef cpy = list_copy<entry_t>
    val expected =
      list_vt2t (reverse (list_vt_mergesort<entry_t> (cpy lst)))
    val gotten = list_vt2t (list_vt_insertion_sort<entry_t> (cpy lst))
  in
    display expected;
    display gotten;
    assertloc (gotten = expected)
  end

implement
main () =
  begin
    test_list
      ($list{entry_t} ((1, 2), (3, 4), (3, 5),
                       (1, 3), (2, 30), (2, 31),
                       (1, 7), (3, 7), (2, 50)));
    test_list_reverse_order
      ($list{entry_t} ((1, 2), (3, 4), (3, 5),
                       (1, 3), (2, 30), (2, 31),
                       (1, 7), (3, 7), (2, 50)));
    0
  end

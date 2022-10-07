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

(* Unit testing. *)

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
    print! "(";
    loop lst;
    println! " )"
  end

fn
test_merge_two_nondecreasing_runs
          {m, n     : nat}
          (lst_m    : list (entry_t, m),
           lst_n    : list (entry_t, n),
           expected : list (entry_t, m + n))
    : void =
  let
    implement
    list_vt_timsort$lt<entry_t> (x, y) =
      (x.0) < (y.0)

    val lst1 = list_copy<entry_t> lst_m
    val lst2 = list_copy<entry_t> lst_n
    val lst3 = merge_two_nondecreasing_runs<entry_t> (lst1, lst2)
    val lst_mn = list_vt2t lst3
  in
    display lst_m;
    display lst_n;
    display lst_mn;
    println! ();
    assertloc (lst_mn = expected)
  end

implement
main () =
  begin

    test_merge_two_nondecreasing_runs
      ($list{entry_t} (),
       $list{entry_t} (),
       $list{entry_t} ());

    test_merge_two_nondecreasing_runs
      ($list{entry_t} ((1, 3)),
       $list{entry_t} ((1, 2)),
       $list{entry_t} ((1, 3), (1, 2)));

    test_merge_two_nondecreasing_runs
      ($list{entry_t} ((4, 6), (4, 5), (10, 7),
                       (10, 3)),
       $list{entry_t} ((4, 4), (5, 3), (10, 2)),
       $list{entry_t} ((4, 6), (4, 5), (4, 4),
                       (5, 3), (10, 7), (10, 3),
                       (10, 2)));

    0
  end

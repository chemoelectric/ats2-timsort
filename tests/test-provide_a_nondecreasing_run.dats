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
test_provide_a_nondecreasing_run
          {n         : int | 2 <= n}
          {minrun    : int | 2 <= minrun}
          {n1, n2    : nat | n1 + n2 == n; min (n, minrun) <= n1}
          (lst       : list (entry_t, n),
           minrun    : int minrun,
           expected1 : list (entry_t, n1),
           expected2 : list (entry_t, n2))
    : void =
  let
    implement
    list_vt_timsort$lt<entry_t> (x, y) =
      (x.0) < (y.0)

    val lst0 = list_copy<entry_t> lst
    val @(lst1, lst2, m) =
      provide_a_nondecreasing_run<entry_t> (lst0, minrun)
    val lst1 = list_vt2t lst1
    and lst2 = list_vt2t lst2
  in
    display lst;
    display lst1;
    display lst2;
    println! ();
    assertloc (lst1 = expected1);
    assertloc (lst2 = expected2);
    assertloc (length lst1 = m)
  end

implement
main () =
  begin

    (* With initial sequence nondecreasing. *)

    test_provide_a_nondecreasing_run
      ($list{entry_t} ((1, 2), (1, 4), (0, 5),
                       (1, 3), (2, 30), (2, 31),
                       (1, 7), (3, 7), (2, 50)),
       2,
       $list{entry_t} ((1, 2), (1, 4)),
       $list{entry_t} ((0, 5), (1, 3), (2, 30),
                       (2, 31), (1, 7), (3, 7),
                       (2, 50)));

    test_provide_a_nondecreasing_run
      ($list{entry_t} ((1, 2), (1, 4), (0, 5),
                       (1, 3), (2, 30), (2, 31),
                       (1, 7), (3, 7), (2, 50)),
       3,
       $list{entry_t} ((0, 5), (1, 2), (1, 4)),
       $list{entry_t} ((1, 3), (2, 30), (2, 31),
                       (1, 7), (3, 7), (2, 50)));

    test_provide_a_nondecreasing_run
      ($list{entry_t} ((1, 2), (1, 4), (0, 5),
                       (1, 3), (2, 30), (2, 31),
                       (1, 7), (3, 7), (2, 50)),
       4,
       $list{entry_t} ((0, 5), (1, 2), (1, 4),
                       (1, 3)),
       $list{entry_t} ((2, 30), (2, 31), (1, 7),
                       (3, 7), (2, 50)));

    test_provide_a_nondecreasing_run
      ($list{entry_t} ((1, 2), (1, 4), (0, 5),
                       (1, 3), (2, 30), (2, 31),
                       (1, 7), (3, 7), (2, 50)),
       100,
       $list{entry_t} ((0, 5), (1, 2), (1, 4),
                       (1, 3), (1, 7), (2, 30),
                       (2, 31), (2, 50), (3, 7)),
       $list{entry_t} ());

    test_provide_a_nondecreasing_run
      ($list{entry_t} ((0, 5), (1, 2), (1, 4),
                       (1, 3), (1, 7), (2, 30),
                       (2, 31), (2, 50), (3, 7)),
       2,
       $list{entry_t} ((0, 5), (1, 2), (1, 4),
                       (1, 3), (1, 7), (2, 30),
                       (2, 31), (2, 50), (3, 7)),
       $list{entry_t} ());

    (* With initial sequence decreasing. *)

    test_provide_a_nondecreasing_run
      ($list{entry_t} ((30, 7), (29, 30), (29, 31),
                       (27, 50), (19, 2), (18, 4),
                       (17, 3), (16, 7), (0, 5)),
       2,
       $list{entry_t} ((29, 30), (30, 7)),
       $list{entry_t} ((29, 31), (27, 50), (19, 2),
                       (18, 4), (17, 3), (16, 7),
                       (0, 5)));

    test_provide_a_nondecreasing_run
      ($list{entry_t} ((30, 7), (29, 30), (29, 31),
                       (27, 50), (19, 2), (18, 4),
                       (17, 3), (16, 7), (0, 5)),
       3,
       $list{entry_t} ((29, 30), (29, 31), (30, 7)),
       $list{entry_t} ((27, 50), (19, 2), (18, 4),
                       (17, 3), (16, 7), (0, 5)));

    test_provide_a_nondecreasing_run
      ($list{entry_t} ((30, 7), (29, 30), (29, 31),
                       (27, 50), (19, 2), (18, 4),
                       (17, 3), (16, 7), (0, 5)),
       4,
       $list{entry_t} ((27, 50), (29, 30), (29, 31),
                       (30, 7)),
       $list{entry_t} ((19, 2), (18, 4), (17, 3),
                       (16, 7), (0, 5)));

    test_provide_a_nondecreasing_run
      ($list{entry_t} ((30, 7), (29, 30), (29, 31),
                       (27, 50), (30, 2), (18, 4),
                       (17, 3), (16, 7), (0, 5)),
       5,
       $list{entry_t} ((27, 50), (29, 30), (29, 31),
                       (30, 7), (30, 2)),
       $list{entry_t} ((18, 4), (17, 3), (16, 7),
                       (0, 5)));

    test_provide_a_nondecreasing_run
      ($list{entry_t} ((30, 7), (29, 30), (29, 31),
                       (27, 50), (30, 2), (18, 4),
                       (27, 3), (16, 7), (0, 5)),
       100,
       $list{entry_t} ((0, 5), (16, 7), (18, 4),
                       (27, 50), (27, 3), (29, 30),
                       (29, 31), (30, 7), (30, 2)),
       $list{entry_t} ());

    test_provide_a_nondecreasing_run
      ($list{entry_t} ((30, 7), (29, 30), (28, 31),
                       (27, 50), (19, 2), (18, 4),
                       (17, 3), (16, 7), (0, 5)),
       2,
       $list{entry_t} ((0, 5), (16, 7), (17, 3),
                       (18, 4), (19, 2), (27, 50),
                       (28, 31), (29, 30), (30, 7)),
       $list{entry_t} ());

    0
  end

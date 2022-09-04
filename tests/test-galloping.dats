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

(* Unit testing of galloping searches. *)

#include "timsort/DATS/array-timsort.dats"

#define NIL list_nil ()
#define ::  list_cons

fn
repeat_int {n : nat}
           (i : int,
            n : int n)
    : list (int, n) =
  let
    fun
    loop {k : nat | k <= n}
         .<n - k>.
         (p : list (int, k),
          k : int k)
        : list (int, n) =
      if k = n then
        p
      else
        loop (i :: p, succ k)
  in
    loop (NIL, 0)
  end

fn
make_sorted_primes () : List1 int =
  let
    val primes = $list (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)

    fun
    loop {n : nat}
         .<n>.
         (result : List int,
          primes : list (int, n))
        : List1 int =
      let
        prval () = lemma_list_param result
      in
        case+ primes of
        | NIL =>
          let
            val () = assertloc (0 < length result)
          in
            result
          end
        | head :: tail =>
          let
            val m = g1ofg0 head
            val () = assertloc (0 <= m)
          in
            loop (repeat_int (head, m) + result, tail)
          end
      end
  in
    loop (NIL, list_vt2t (reverse primes))
  end

extern fn {}
check_pos$pred :
  (int, int) -<> bool

fun {}
check_pos {n   : nat}
          {pos : nat | pos <= n}
          (arr : &array (int, n),
           n   : size_t n,
           x   : int,
           pos : size_t pos)
    : void =
  let
    var i : [i : nat | i <= n] size_t i
  in
    for (i := i2sz 0; i != n; i := succ i)
      if i < pos then
        assertloc (check_pos$pred<> (arr[i], x))
      else
        assertloc (~check_pos$pred<> (arr[i], x))
  end

extern fn {}
check_many_pos$find_pos :
  {p_arr : addr}
  {n     : pos}
  {hint  : nat | hint <= n - 1}
  {p_x0  : addr}
  {n_x0  : int}
  {i_x   : nat | i_x <= n_x0 - 1}
  (!array_v (int, p_arr, n),
   !array_v (int, p_x0, n_x0) |
   bptr_anchor (int, p_arr),
   bptr (int, p_arr, n),
   size_t hint,
   bptr (int, p_x0, i_x)) -<>
    [j : nat | j <= n]
    bptr (int, p_arr, j)

fun {}
check_many_pos
          {n   : nat}
          (arr : &array (int, n),
           n   : size_t n)
    : void =
  let
    val bp_arr = ptr2bptr_anchor (addr@ arr)

    var pos : int
  in
    for (pos := ~100; pos <> 201; pos := succ pos)
      let
        var hint : [hint : nat | hint <= n] size_t hint
      in
        for (hint := i2sz 0; hint <> n; hint := succ hint)
          let
            var x = @[int][1] (0)
            val bp_x = ptr2bptr_anchor (addr@ x)

            val () = x[0] := pos
            val bp =
              check_many_pos$find_pos<>
                (view@ arr, view@ x | bp_arr, bp_arr + n, hint, bp_x)
          in
            check_pos<> (arr, n, pos, bp - bp_arr)
          end
      end
  end

fun
check_many_pos_lt_left
          {n   : nat}
          (arr : &array (int, n),
           n   : size_t n)
    : void =
  let
    implement
    check_pos$pred<> (x, y) =
      x < y
    
    implement
    check_many_pos$find_pos<> (pf_arr, pf_x0 |
                               bp_arr, bp_n, hint, bp_x) =
      find_1st_position_past_lt_x<int>
        (pf_arr, pf_x0 | bp_arr, bp_n, hint, bp_x)
  in
    check_many_pos<> (arr, n)
  end

fun
check_many_pos_lte_left
          {n   : nat}
          (arr : &array (int, n),
           n   : size_t n)
    : void =
  let
    implement
    check_pos$pred<> (x, y) =
      x <= y
    
    implement
    check_many_pos$find_pos<> (pf_arr, pf_x0 |
                               bp_arr, bp_n, hint, bp_x) =
      find_1st_position_past_lte_x<int>
        (pf_arr, pf_x0 | bp_arr, bp_n, hint, bp_x)
  in
    check_many_pos<> (arr, n)
  end

fn
test_lt_on_left_with_sorted_primes () : void =
  let
    val primes_lst = make_sorted_primes ()
    val n = length primes_lst

    val @(pf_arr, pfgc_arr | p_arr) = array_ptr_alloc<int> (i2sz n)
  in
    array_initize_list<int> (!p_arr, n, primes_lst);
    check_many_pos_lt_left (!p_arr, i2sz n);
    array_ptr_free (pf_arr, pfgc_arr | p_arr)
  end

fn
test_lte_on_left_with_sorted_primes () : void =
  let
    val primes_lst = make_sorted_primes ()
    val n = length primes_lst

    val @(pf_arr, pfgc_arr | p_arr) = array_ptr_alloc<int> (i2sz n)
  in
    array_initize_list<int> (!p_arr, n, primes_lst);
    check_many_pos_lte_left (!p_arr, i2sz n);
    array_ptr_free (pf_arr, pfgc_arr | p_arr)
  end

implement
main () =
  begin
    test_lt_on_left_with_sorted_primes ();
    test_lte_on_left_with_sorted_primes ();
    0
  end

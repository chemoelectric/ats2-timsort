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

(* Unit testing of merges. *)

#include "timsort/DATS/array-timsort.dats"

#define NIL list_nil ()
#define ::  list_cons

fn {a : t@ype}
array_init_from_list
          {p_arr  : addr}
          {n      : int}
          (pf_arr : !array_v (a?, p_arr, n) >> array_v (a, p_arr, n) |
           p_arr  : ptr p_arr,
           n      : int n,
           lst    : list (a, n))
    :<!wrt> void =
  array_initize_list<a> (!p_arr, n, lst)

typedef entry_t =
  @{
    key = int,
    value = int
  }

implement
array_timsort$lt<entry_t> (x, y) =
  (x.key) < (y.key)

implement
list_mergesort$cmp<entry_t> (x, y) =
  if (x.key) < (y.key) then
    ~1
  else if (x.key) > (y.key) then
    1
  else
    0

implement
list_equal$eqfn<entry_t> (x, y) =
  ((x.key) = (y.key)) * ((x.value) = (y.value))

fn
repeat_int_key
          {n            : nat}
          (i            : int,
           n            : int n,
           value_offset : int)
    : list (entry_t, n) =
  let
    fun
    loop {k : nat | k <= n}
         .<n - k>.
         (p : list (entry_t, k),
          k : int k)
        : list (entry_t, n) =
      if k = n then
        list_vt2t (reverse p)
      else
        let
          val entry =
            @{
              key = i,
              value = g0ofg1 k + value_offset
            }
        in
          loop (entry :: p, succ k)
        end
  in
    loop (NIL, 0)
  end

fn
make_sorted_primes_entries
          (value_offset : int)
    : List1 entry_t =
  let
    val primes = $list (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)

    fun
    loop {n : nat}
         .<n>.
         (result : List entry_t,
          primes : list (int, n))
        : List1 entry_t =
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
            loop (repeat_int_key (head, m, value_offset) + result,
                  tail)
          end
      end
  in
    loop (NIL, list_vt2t (reverse primes))
  end

fun
display {n : nat}
        (p : list (entry_t, n))
    : void =
  case+ p of
  | NIL => ()
  | head :: tail =>
    begin
      println! (head.key, " -> ", head.value);
      display tail
    end

fn
test_merge_left_with_primes () : void =
  let
    val lst_left = make_sorted_primes_entries (1)
    and lst_right =
      list_vt2t (list_mergesort<entry_t>
                   (make_sorted_primes_entries (1000)
                      + make_sorted_primes_entries (2000)))

    val n_left = length lst_left
    and n_right = length lst_right
    val () = assertloc (n_left <= n_right)

    val n = n_left + n_right

    prval [n_left : int] EQINT () = eqint_make_gint n_left
    prval [n_right : int] EQINT () = eqint_make_gint n_right
    stadef n = n_left + n_right

    val [p_arr : addr] @(pf_arr, pfgc_arr | p_arr) =
      array_ptr_alloc<entry_t> (i2sz n)
    val [p_work : addr] @(pf_work, pfgc_work | p_work) =
      array_ptr_alloc<entry_t> (i2sz (half n + 1))

    val p_left = p_arr
    and p_right = ptr_add<entry_t> (p_arr, n_left)

    prval @(pf_left, pf_right) =
      array_v_split {entry_t?} {p_arr} {n} {n_left} pf_arr
    val () = array_init_from_list (pf_left | p_left, n_left, lst_left)
    val () = array_init_from_list (pf_right | p_right, n_right,
                                              lst_right)
    prval () = pf_arr := array_v_unsplit (pf_left, pf_right)

    val bp_arr = ptr2bptr_anchor p_arr
    and bp_work = ptr2bptr_anchor p_work

    val bp_i = bp_arr + n_left
    and bp_n = bp_arr + n

    var params : merge_params_vt
    val () = initialize_gallop_thresholds params
    val () =
      merge_left<entry_t>
        {p_arr} {n} {n_left} {p_work} {(n / 2) + 1}
        (pf_arr, pf_work | bp_arr, bp_i, bp_n, bp_work, params)

    val gotten =
      list_vt2t (array_copy_to_list_vt<entry_t> (!p_arr, i2sz n))
    and expected =
      list_vt2t (list_mergesort<entry_t> (lst_left + lst_right))

    //val () = display gotten
    //val () = display expected

    val () = assertloc (gotten = expected)

    val () = array_ptr_free (pf_arr, pfgc_arr | p_arr)
    and () = array_ptr_free (pf_work, pfgc_work | p_work)
  in
  end

fn
test_merge_right_with_primes () : void =
  let
    val lst_left =
      list_vt2t (list_mergesort<entry_t>
                   (make_sorted_primes_entries (1000)
                      + make_sorted_primes_entries (2000)))
    and lst_right = make_sorted_primes_entries (1)

    val n_left = length lst_left
    and n_right = length lst_right
    val () = assertloc (n_left >= n_right)

    val n = n_left + n_right

    prval [n_left : int] EQINT () = eqint_make_gint n_left
    prval [n_right : int] EQINT () = eqint_make_gint n_right
    stadef n = n_left + n_right

    val [p_arr : addr] @(pf_arr, pfgc_arr | p_arr) =
      array_ptr_alloc<entry_t> (i2sz n)
    val [p_work : addr] @(pf_work, pfgc_work | p_work) =
      array_ptr_alloc<entry_t> (i2sz (half n + 1))

    val p_left = p_arr
    and p_right = ptr_add<entry_t> (p_arr, n_left)

    prval @(pf_left, pf_right) =
      array_v_split {entry_t?} {p_arr} {n} {n_left} pf_arr
    val () = array_init_from_list (pf_left | p_left, n_left, lst_left)
    val () = array_init_from_list (pf_right | p_right, n_right,
                                              lst_right)
    prval () = pf_arr := array_v_unsplit (pf_left, pf_right)

    val bp_arr = ptr2bptr_anchor p_arr
    and bp_work = ptr2bptr_anchor p_work

    val bp_i = bp_arr + n_left
    and bp_n = bp_arr + n

    var params : merge_params_vt
    val () = initialize_gallop_thresholds params
    val () =
      merge_right<entry_t>
        {p_arr} {n} {n_left} {p_work} {(n / 2) + 1}
        (pf_arr, pf_work | bp_arr, bp_i, bp_n, bp_work, params)

    val gotten =
      list_vt2t (array_copy_to_list_vt<entry_t> (!p_arr, i2sz n))
    and expected =
      list_vt2t (list_mergesort<entry_t> (lst_left + lst_right))

    //val () = display gotten
    //val () = display expected

    val () = assertloc (gotten = expected)

    val () = array_ptr_free (pf_arr, pfgc_arr | p_arr)
    and () = array_ptr_free (pf_work, pfgc_work | p_work)
  in
  end

implement
main () =
  begin
    test_merge_left_with_primes ();
    test_merge_right_with_primes ();
    0
  end

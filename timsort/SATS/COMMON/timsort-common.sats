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

#define ATS_PACKNAME "ats2-timsort"
#define ATS_EXTERN_PREFIX "ats2_timsort_"

%{#
#include <timsort/CATS/timsort.cats>
#include <timsort/CATS/bptr.cats>
%}

(*------------------------------------------------------------------*)

prfn
lemma_mul_isfun :               (* Multiplication is a function. *)
  {m1, n1 : int}
  {m2, n2 : int | m1 == m2; n1 == n2}
  () -<prf>
    [m1 * n1 == m2 * n2]
    void

prfn
lemma_mul_commutes :            (* Multiplication is commutative. *)
  {m, n : int}
  () -<prf>
    [m * n == n * m]
    void

prfn
array_v_takeout2 :     (* Get views for two distinct array elements.*)
  {a     : vt@ype}
  {p     : addr}
  {n     : int}
  {i, j  : nat | i < n; j < n; i != j}
  array_v (a, p, n) -<prf>
    @(a @ p + (i * sizeof a),
      a @ p + (j * sizeof a),
      (a @ p + (i * sizeof a),
       a @ p + (j * sizeof a)) -<prf,lin>
        array_v (a, p, n))

(*------------------------------------------------------------------*)

fn
char_bit :
  () -<> [char_bit : pos] size_t char_bit

(*------------------------------------------------------------------*)

fn {tk : tkind}
g0uint_ceildiv :
  (g0uint tk, g0uint tk) -<> g0uint tk

fn {tk : tkind}
g1uint_ceildiv :
  {m, n : int | 0 <= m; 1 <= n}
  (g1uint (tk, m), g1uint (tk, n)) -<>
    [q : int | q * n == m || q * n == m + 1]
    g1uint (tk, q)

overload ceildiv with g0uint_ceildiv of 0
overload ceildiv with g1uint_ceildiv of 10

fn {tk : tkind}
g0uint_is_even :
  g0uint tk -<> bool

fn {tk : tkind}
g0uint_is_odd :
  g0uint tk -<> bool

fn {tk : tkind}
g1uint_is_even :
  {n : int}
  g1uint (tk, n) -<> bool (n mod 2 == 0)

fn {tk : tkind}
g1uint_is_odd :
  {n : int}
  g1uint (tk, n) -<> bool (n mod 2 == 1)

overload is_even with g0uint_is_even of 0
overload is_odd with g0uint_is_odd of 0
overload is_even with g1uint_is_even of 10
overload is_odd with g1uint_is_odd of 10

fn {tk : tkind}
g0uint_clz :
  g0uint tk -<> int

fn {tk : tkind}
g1uint_clz :
  {n : nat}
  g1uint (tk, n) -<>
    [i : nat]
    int i

overload clz with g0uint_clz of 0
overload clz with g1uint_clz of 10

(*------------------------------------------------------------------*)

fn
g1uint_double_size :
  g1uint_double_type sizeknd = "mac#%"

fn
g0uint_ceildiv_size :
  (size_t, size_t) -<> size_t = "mac#%"

fn
g1uint_ceildiv_size :
  {m, n : int | 0 <= m; 1 <= n}
  (size_t m, size_t n) -<>
    [q : int | q * n == m || q * n == m + 1]
    size_t q = "mac#%"

fn
g0uint_is_even_size :
  size_t -<> bool = "mac#%"

fn
g1uint_is_even_size :
  {n : int}
  size_t n -<> bool (n mod 2 == 0) = "mac#%"

fn
g0uint_is_odd_size :
  size_t -<> bool = "mac#%"

fn
g1uint_is_odd_size :
  {n : int}
  size_t n -<> bool (n mod 2 == 1) = "mac#%"

fn
g0uint_clz_ullint :
  ullint -<> int = "mac#%"

fn
g1uint_clz_ullint :
  {n : nat}
  ullint n -<>
    [i : nat]
    int i = "mac#%"

fn
g0uint_clz_size :
  size_t -<> int = "mac#%"

fn
g1uint_clz_size :
  {n : nat}
  size_t n -<>
    [i : nat]
    int i = "mac#%"

(*------------------------------------------------------------------*)
(* Node power for the powersort merge strategy.                     *)

fn
nodepower {n      : int}
          {i      : nat}
          {n1, n2 : pos | i + n1 + n2 <= n}
          (n      : size_t n,
           i      : size_t i,
           n1     : size_t n1,
           n2     : size_t n2)
    :<> [power : int]
        int power = "mac#%"

(*------------------------------------------------------------------*)
(* A stack of subarray boundaries.                                  *)

typedef stk_entry_t (index : int, size : int, power : int) =
  @{
    index = size_t index,      (* The subarray begins at this index.*)
    size = size_t size,        (* The subarray has this length. *)
    power = int power   (* The node power, if it has been computed. *)
  }
typedef stk_entry_t =
  [index, size, power : int]
  stk_entry_t (index, size, power)

vtypedef stk_vt (p        : addr,
                 depth    : int,
                 stk_max  : int) =
  @{
    pf       = array_v (stk_entry_t, p, stk_max) |
    p        = ptr p,
    depth    = int depth,
    stk_max  = size_t stk_max
  }

fn {}
stk_vt_make :
  {p       : addr}
  {stk_max : int}
  (array_v (stk_entry_t, p, stk_max) | ptr p, size_t stk_max) -<>
    stk_vt (p, 0, stk_max)

fn {}
stk_vt_depth :
  {p_stk   : addr}
  {stk_max : int}
  {depth   : nat}
  (&stk_vt (p_stk, depth, stk_max)) -<> int depth

fn {}
stk_vt_push :
  {p_stk   : addr}
  {stk_max : int}
  {depth   : nat | depth < stk_max}
  {index   : nat}
  {size    : pos}
  {power   : int}
  (size_t index,
   size_t size,
   int power,
   &stk_vt (p_stk, depth, stk_max)
        >> stk_vt (p_stk, depth + 1, stk_max)) -< !wrt >
    void

fn {}
stk_vt_peek :
  {p_stk     : addr}
  {stk_max   : int}
  {depth     : int | depth < stk_max}
  {entry_num : nat | entry_num < depth}
  (&stk_vt (p_stk, depth, stk_max),
   int entry_num) -< !wrt >
    [index, size, power : int]
    stk_entry_t (index, size, power)

fn {}
stk_vt_set_power :
  {power     : int}
  {p_stk     : addr}
  {stk_max   : int}
  {depth     : int | depth < stk_max}
  {entry_num : nat | entry_num < depth}
  (int power,
   &stk_vt (p_stk, depth, stk_max),
   int entry_num) -< !wrt >
    void

fn {}
stk_vt_drop :
  {p_stk   : addr}
  {stk_max : int}
  {depth   : pos | depth < stk_max}
  (&stk_vt (p_stk, depth, stk_max)
        >> stk_vt (p_stk, depth - 1, stk_max)) -< !wrt >
    void

(*------------------------------------------------------------------*)

(* Compute a minimum run length. Runs shorter than this will be
   extended via an insertion sort. *)
fn {}
minimum_run_length :
  {n : int}
  size_t n -<>
    [minrun : int | min (n, 32) <= minrun; minrun <= 64]
    size_t minrun

(*------------------------------------------------------------------*)

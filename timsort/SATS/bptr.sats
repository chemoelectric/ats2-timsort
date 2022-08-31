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

#define ATS_PACKNAME "ats2-timsort-bptr"
#define ATS_EXTERN_PREFIX "ats2_timsort_bptr_"

%{#
#include <timsort/CATS/bptr.cats>
%}

(*------------------------------------------------------------------*)
(* A bptr is similar to an aptr, but is specially suited for        *)
(* accessing the elements of arrays.                                *)

abst@ype bptr (a : vt@ype+, p : addr, i : int) = ptr

typedef bptr_anchor (a : vt@ype+, p : addr) =
  bptr (a, p, 0)

fn {a : vt@ype}
ptr2bptr_anchor :
  {p : addr}
  ptr p -<> bptr_anchor (a, p)

fn
bptr_anchor2ptr :
  {a : vt@ype}
  {p : addr}
  bptr_anchor (a, p) -<> ptr p = "mac#%"

fn {a : vt@ype}
bptr2ptr :
  {p : addr}
  {i : int}
  (bptr (a, p, i)) -<> ptr (p + (i * sizeof a))

fn {a : vt@ype}
bptr_reanchor :
  {p : addr}
  {i : int}
  bptr (a, p, i) -<> bptr_anchor (a, p + (i * sizeof a))

(*------------------------------------------------------------------*)

fn {a  : vt@ype}
   {tk : tkind}
bptr_add_g1uint :
  {p : addr}
  {i : int}
  {j : int}
  (bptr (a, p, i), g1uint (tk, j)) -<> bptr (a, p, i + j)

fn {a  : vt@ype}
   {tk : tkind}
bptr_add_g1int :
  {p : addr}
  {i : int}
  {j : int}
  (bptr (a, p, i), g1int (tk, j)) -<> bptr (a, p, i + j)

overload bptr_add with bptr_add_g1uint
overload bptr_add with bptr_add_g1int
overload + with bptr_add of 30

(*------------------------------------------------------------------*)

fn {a  : vt@ype}
   {tk : tkind}
bptr_sub_g1uint :
  {p : addr}
  {i : int}
  {j : int}
  (bptr (a, p, i), g1uint (tk, j)) -<> bptr (a, p, i - j)

fn {a  : vt@ype}
   {tk : tkind}
bptr_sub_g1int :
  {p : addr}
  {i : int}
  {j : int}
  (bptr (a, p, i), g1int (tk, j)) -<> bptr (a, p, i - j)

overload bptr_sub with bptr_sub_g1uint
overload bptr_sub with bptr_sub_g1int
overload - with bptr_sub of 30

(*------------------------------------------------------------------*)

fn {a : vt@ype}
bptr_succ :
  {p : addr}
  {i : int}
  bptr (a, p, i) -<> bptr (a, p, i + 1)

fn {a : vt@ype}
bptr_pred :
  {p : addr}
  {i : int}
  bptr (a, p, i) -<> bptr (a, p, i - 1)

overload succ with bptr_succ of 30
overload pred with bptr_pred of 30

(*------------------------------------------------------------------*)

fn {a : vt@ype}
bptr_diff :
  {p    : addr}
  {i, j : int | i >= j}
  (bptr (a, p, i), bptr (a, p, j)) -<> size_t (i - j)

overload - with bptr_diff of 30

(*------------------------------------------------------------------*)

fn
lt_bptr_bptr :
  {a : vt@ype}
  {p    : addr}
  {i, j : int}
  (bptr (a, p, i), bptr (a, p, j)) -<> bool (i < j) = "mac#%"

fn
lte_bptr_bptr :
  {a : vt@ype}
  {p    : addr}
  {i, j : int}
  (bptr (a, p, i), bptr (a, p, j)) -<> bool (i <= j) = "mac#%"

fn
gt_bptr_bptr :
  {a    : vt@ype}
  {p    : addr}
  {i, j : int}
  (bptr (a, p, i), bptr (a, p, j)) -<> bool (i > j) = "mac#%"

fn
gte_bptr_bptr :
  {a    : vt@ype}
  {p    : addr}
  {i, j : int}
  (bptr (a, p, i), bptr (a, p, j)) -<> bool (i >= j) = "mac#%"

fn
eq_bptr_bptr :
  {a    : vt@ype}
  {p    : addr}
  {i, j : int}
  (bptr (a, p, i), bptr (a, p, j)) -<> bool (i == j) = "mac#%"

fn
neq_bptr_bptr :
  {a    : vt@ype}
  {p    : addr}
  {i, j : int}
  (bptr (a, p, i), bptr (a, p, j)) -<> bool (i != j) = "mac#%"

fn
compare_bptr_bptr :
  {a    : vt@ype}
  {p    : addr}
  {i, j : int}
  (bptr (a, p, i), bptr (a, p, j)) -<> int (sgn (i - j)) = "mac#%"

overload < with lt_bptr_bptr of 30
overload <= with lte_bptr_bptr of 30
overload > with gt_bptr_bptr of 30
overload >= with gte_bptr_bptr of 30
overload = with eq_bptr_bptr of 30
overload <> with neq_bptr_bptr of 30
overload != with neq_bptr_bptr of 30
overload compare with compare_bptr_bptr of 30

(*------------------------------------------------------------------*)

fn {a : vt@ype}
bptr_get :
  {p : addr}
  {i : int}
  (!a @ (p + (i * sizeof a)) >> a?! @ (p + (i * sizeof a)) |
   bptr (a, p, i)) -<>
    a

fn {a : vt@ype}
bptr_set :
  {p : addr}
  {i : int}
  (!a? @ (p + (i * sizeof a)) >> a @ (p + (i * sizeof a)) |
   bptr (a, p, i),
   a) -< !wrt >
    void

fn {a : vt@ype}
bptr_exch :
  {p : addr}
  {i : int}
  (!a @ (p + (i * sizeof a)) |
   bptr (a, p, i),
   &a >> a) -< !wrt >
    void

(* Interchange two elements of an array. *)
fn {a : vt@ype}
interchange_bptr_bptr :
  {p : addr}
  {n : int}
  {i, j : nat | i <= n - 1; j <= n - 1}
  (!array_v (a, p, n) |
   bptr (a, p, i),
   bptr (a, p, j)) -< !wrt >
    void

(* Reverse a subarray. The first bptr points at the first element. The
   second bptr points at one position past the last element. (These
   arguments are chosen for consistency with the prelude’s
   array_subreverse.) *)
fn {a : vt@ype}
subreverse_bptr_bptr :
  {p    : addr}
  {n    : int}
  {i, j : int | 0 <= i; i < j; j <= n}
  (!array_v (a, p, n) |
   bptr (a, p, i),
   bptr (a, p, j)) -< !wrt >
    void

(* Circular rotation right by one element. The value at the jth
   position gets moved to the ith position. *)
fn {a : vt@ype}
subcirculate_right_bptr_bptr :
  {p    : addr}
  {n    : int}
  {i, j : int | 0 <= i; i <= j; j <= n - 1}
  (!array_v (a, p, n) |
   bptr (a, p, i),
   bptr (a, p, j)) -< !wrt >
    void

(* Circular rotation right by one element, with a ‘gap’ (a positive
   stride). The value at the (i + (m * gap))th position gets moved to
   the ith position. NOTE: most likely you will have to supply some of
   the static arguments. *)
fn {a : vt@ype}
subcirculate_right_with_gap_bptr_bptr :
  {p         : addr}
  {n         : int}
  {i, m, gap : int | 0 <= i; 0 <= m; 1 <= gap;
                     i + (m * gap) <= n - 1}
  (!array_v (a, p, n) |
   bptr (a, p, i),
   bptr (a, p, i + (m * gap)),
   size_t gap) -< !wrt >
    void

(* Copy elements from one array to a different array. Overlap is not
   checked for at runtime, but is implicitly rejected by the need for
   separate views. *)
fn {a : vt@ype}
copy_bptr_bptr_size :
  {dst : addr}
  {src : addr}
  {n   : int}
  (!array_v (a?, dst, n) >> array_v (a, dst, n),
   !array_v (a, src, n) >> array_v (a?!, src, n) |
   bptr_anchor (a?, dst),
   bptr_anchor (a, src),
   size_t n) -< !wrt >
    void

(* Copy elements from one array to a different array. Overlap is not
   checked for at runtime, but is implicitly rejected by the need for
   separate views. *)
fn {a : vt@ype}
copy_bptr_bptr_bptr :
  {dst : addr}
  {src : addr}
  {n   : int}
  (!array_v (a?, dst, n) >> array_v (a, dst, n),
   !array_v (a, src, n) >> array_v (a?!, src, n) |
   bptr_anchor (a?, dst),
   bptr_anchor (a, src),
   bptr (a, src, n)) -< !wrt >
    void

overload copy_bptr_bptr with copy_bptr_bptr_size
overload copy_bptr_bptr with copy_bptr_bptr_bptr

overload interchange with interchange_bptr_bptr of 30
overload subreverse with subreverse_bptr_bptr of 30
overload subcirculate_right with subcirculate_right_bptr_bptr of 30
overload subcirculate_right_with_gap with
  subcirculate_right_with_gap_bptr_bptr of 30
overload copy with copy_bptr_bptr of 30

(*------------------------------------------------------------------*)

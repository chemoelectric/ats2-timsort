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

staload "timsort/SATS/COMMON/timsort-common.sats"

(*------------------------------------------------------------------*)

fn {a : vt@ype}
list_vt_timsort :
  {n : int}
  list_vt (a, n) -< !wrt > list_vt (a, n)

(* Implement either list_vt_timsort$lt or list_vt_timsort$cmp.
   The former takes precedence. The latter defaults to
   ‘gcompare_ref_ref<a>’. *)
fn {a : vt@ype}
list_vt_timsort$lt :
  (&a, &a) -<> bool
fn {a : vt@ype}
list_vt_timsort$cmp :
  (&a, &a) -<> int

(*------------------------------------------------------------------*)

(* Note that list_timsort returns a ‘list_vt’ rather than a ‘list’.
   The prelude’s list_mergesort does likewise. Use list_vt2t to get
   a non-linear list from the result. *)
fn {a : t@ype}
list_timsort :
  {n : int}
  list (a, n) -< !wrt > list_vt (a, n)

(* Implement either list_timsort$lt or list_timsort$cmp.  The former
   takes precedence. The latter defaults to
   ‘gcompare_ref_ref<a>’. Note that the prelude uses call by value
   rather than call by reference, but call by reference seems better
   if keys and values are not treated separately. *)
fn {a : t@ype}
list_timsort$lt :
  (&a, &a) -<> bool
fn {a : t@ype}
list_timsort$cmp :
  (&a, &a) -<> int

(*------------------------------------------------------------------*)

(* The following routines return a ‘list_vt’ rather than a ‘list’.
   The prelude’s list sorts do likewise. Use list_vt2t to get a
   non-linear list from the result. *)

fn {a : t@ype}
list_timsort_fun :
  {n : int}
  (list (a, n),
   (&a, &a) -<> bool) -< !wrt >
    list_vt (a, n)

fn {a : t@ype}
list_timsort_cloref :
  {n : int}
  (list (a, n),
   (&a, &a) -<cloref> bool) -< !wrt >
    list_vt (a, n)

(*------------------------------------------------------------------*)

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

staload "timsort/SATS/array-timsort.sats"
staload "timsort/SATS/COMMON/timsort-common.sats"
staload _ = "timsort/DATS/COMMON/timsort-common.dats"

(*------------------------------------------------------------------*)

(* Compute a minimum run length. Runs shorter than this will be
   extended via an insertion sort. *)
extern fn {}
minimum_run_length :
  {n : nat}
  size_t n -<>
    [minrun : nat | minrun <= 64]
    size_t minrun

(*------------------------------------------------------------------*)

implement {}
minimum_run_length {n} n =
  if n < i2sz 64 then
    n       (* The array to be sorted is small. Use insertion sort. *)
  else
    (* The algorithm here is similar to that used in Python’s
       listsort, and tries to divide up n into a number of runs that
       is either a power of two or is close to but less than a power
       of two. *)
    let
      fun
      loop1 {q : nat}
            .<q>.
            (q : size_t q)
          :<> [minrun : nat | minrun <= 64]
              size_t minrun =
        if q < 64 then
          succ q
        else
          loop1 (half q)

      fun
      loop0 {q : nat}
            .<q>.
            (q : size_t q)
          :<> [minrun : nat | minrun <= 64]
              size_t minrun =
        if q < 64 then
          q
        else if is_even q then
          loop0 (half q)
        else
          loop1 (half q)
    in
      loop0 n
    end

(*------------------------------------------------------------------*)


(* /* Compute a good value for the minimum run length; natural runs shorter *)
(*  * than this are boosted artificially via binary insertion. *)
(*  * *)
(*  * If n < 64, return n (it's too small to bother with fancy stuff). *)
(*  * Else if n is an exact power of 2, return 32. *)
(*  * Else return an int k, 32 <= k <= 64, such that n/k is close to, but *)
(*  * strictly less than, an exact power of 2. *)
(*  * *)
(*  * See listsort.txt for more info. *)
(*  */ *)
(* static Py_ssize_t *)
(* merge_compute_minrun(Py_ssize_t n) *)
(* { *)
(*     Py_ssize_t r = 0;           /* becomes 1 if any 1 bits are shifted off */ *)

(*     assert(n >= 0); *)
(*     while (n >= 64) { *)
(*         r |= n & 1; *)
(*         n >>= 1; *)
(*     } *)
(*     return n + r; *)
(* } *)

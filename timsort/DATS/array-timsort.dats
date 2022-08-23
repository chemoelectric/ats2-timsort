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
    [minrun : int | min (n, 32) <= minrun; minrun <= 64]
    size_t minrun

(*------------------------------------------------------------------*)

implement {}
minimum_run_length n =
  if n < i2sz 64 then
    n       (* The array to be sorted is small. Use insertion sort. *)
  else
    (* The algorithm here is similar to that used in Python’s
       listsort, and tries to divide up n into a number of runs that
       is either a power of two or is close to but less than a power
       of two. *)
    let
      fun
      loop1 {q : int | 32 <= q}
            .<q>.
            (q : size_t q)
          :<> [minrun : int | 32 <= minrun; minrun <= 64]
              size_t minrun =
        if q < 64 then
          succ q
        else
          loop1 (half q)

      fun
      loop0 {q : int | 32 <= q}
            .<q>.
            (q : size_t q)
          :<> [minrun : int | 32 <= minrun; minrun <= 64]
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

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

#define ATS_PACKNAME "ats2-timsort-c"
#define ATS_EXTERN_PREFIX "ats2_timsort_c_"

#include "share/atspre_staload.hats"
#include "timsort/HATS/array-timsort.hats"
staload UN = "prelude/SATS/unsafe.sats"

#define PTRS_THRESHOLD 512

%{^

#include "ats2-timsort.h"
#include "timsort-for-c-memory.h"

#if defined __GNUC__
#define ats2_timsort_c_memcpy __builtin_memcpy
#else
#define ats2_timsort_c_memcpy memcpy
#endif

%}

extern fn
ats2_timsort_c_timsort_to_array
          {nmemb, sz : int}
          (result    : &array (byte?, nmemb * sz)
                        >> array (byte, nmemb * sz),
           arr       : &array (byte, nmemb * sz),
           n         : size_t nmemb,
           sz        : size_t sz,
           less_than : (ptr, ptr) -<fun> int)
    : void = "ext#ats2_timsort_c_timsort_to_array"

fn
fill_pointers
          {p_arr     : addr}
          {nmemb, sz : int}
          (p_arr     : ptr p_arr,
           nmemb     : size_t nmemb,
           sz        : size_t sz,
           ptrs      : &array (ptr?, nmemb) >> array (ptr, nmemb))
    : void =
  let
    prval () = lemma_g1uint_param nmemb

    fun
    loop {k      : nat | k <= nmemb}
         {p_ptrs : addr}
         .<k>.
         (pf_ptrs : !array_v (ptr?, p_ptrs, k)
                      >> array_v (ptr, p_ptrs, k) |
          p_ptrs  : ptr p_ptrs,
          k       : size_t k)
        : void =
      if k = i2sz 0 then
        let
          prval () = pf_ptrs := array_v_unnil_nil pf_ptrs
        in
        end
      else
        let
          prval @(pf_ptrs1, pf_p) = array_v_unextend pf_ptrs
          val k1 = pred k
          val () = ptr_set<ptr> (pf_p |
                                 ptr_add<ptr> (p_ptrs, k1),
                                 ptr_add<byte> (p_arr, k1 * sz))
          val () = loop (pf_ptrs1 | p_ptrs, k1)
          prval () = pf_ptrs := array_v_extend (pf_ptrs1, pf_p)
        in
        end
  in
    loop (view@ ptrs | addr@ ptrs, nmemb)
  end

fn
copy_elements
          {p_arr     : addr}
          {nmemb, sz : int}
          (result    : &array (byte?, nmemb * sz)
                        >> array (byte, nmemb * sz),
           arr       : &array (byte, nmemb * sz),
           nmemb     : size_t nmemb,
           sz        : size_t sz,
           ptrs      : &array (ptr, nmemb))
    : void =
  let
    prval () = lemma_g1uint_param nmemb

    fun
    loop {k        : nat | k <= nmemb}
         {p_result : addr}
         .<k>.
         (p_result : ptr p_result,
          ptrs     : &array (ptr, nmemb),
          k        : size_t k)
        : void =
      if k <> i2sz 0 then
        let
          val k1 = pred k
          val _ = $extfcall (ptr, "ats2_timsort_c_memcpy",
                             ptr_add<byte> (p_result, k1 * sz),
                             ptrs[k1], sz)
        in
          loop (p_result, ptrs, k1)
        end

    prval () = $UN.castvwtp2void{array (byte, nmemb * sz)} result
  in
    loop (addr@ result, ptrs, nmemb)
  end

implement
ats2_timsort_c_timsort_to_array {nmemb, sz}
                                (result, arr, nmemb, sz,
                                 less_than) =
  let
    implement
    array_timsort$lt<ptr> (x, y) =
      (x \less_than y) <> 0

    fn
    sort {nmemb, sz : int}
         (result    : &array (byte?, nmemb * sz)
                       >> array (byte, nmemb * sz),
          arr       : &array (byte, nmemb * sz),
          nmemb     : size_t nmemb,
          sz        : size_t sz,
          less_than : (ptr, ptr) -<fun> int,
          ptrs      : &array (ptr?, nmemb) >> array (ptr, nmemb))
        : void =
      begin
        fill_pointers (addr@ arr, nmemb, sz, ptrs);
        array_timsort<ptr> (ptrs, nmemb);
        copy_elements (result, arr, nmemb, sz, ptrs)
      end
  in
    if nmemb <= i2sz PTRS_THRESHOLD then
      let
        prval () = lemma_g1uint_param nmemb
        var storage : @[ptr?][PTRS_THRESHOLD]
        prval @(pf_ptrs, pf_unused) =
          array_v_split {ptr?} {..} {PTRS_THRESHOLD} {nmemb}
                        (view@ storage)
        val () = sort (result, arr, nmemb, sz, less_than,
                       !(addr@ storage))
        prval () = view@ storage :=
          array_v_unsplit (pf_ptrs, pf_unused)
      in
      end
    else
      let
        val @(pf_ptrs, pfgc_ptrs | p_ptrs) =
          array_ptr_alloc<ptr> nmemb
      in
        sort (result, arr, nmemb, sz, less_than, !p_ptrs);
        array_ptr_free (pf_ptrs, pfgc_ptrs | p_ptrs)
      end
  end

%{
/* An addressable instantiation of the inline subroutine. */
extern inline void
timsort_to_array (void *result, const void *arr,
                  size_t nmemb, size_t sz,
                  ats2_timsort_c_bool ( *less_than )
                    (const void *, const void *));
%}

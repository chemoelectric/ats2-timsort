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

#define ATS_PACKNAME "ats2-timsort-bptr"
#define ATS_EXTERN_PREFIX "ats2_timsort_bptr_"

#include "share/atspre_staload.hats"
staload "timsort/SATS/bptr.sats"
staload UN = "prelude/SATS/unsafe.sats"

prfn
lemma_mul_isfun
          {m1, n1 : int}
          {m2, n2 : int | m1 == m2; n1 == n2}
          ()
    :<prf> [m1 * n1 == m2 * n2]
           void =
  let
    prval pf1 = mul_make {m1, n1} ()
    prval pf2 = mul_make {m2, n2} ()
    prval () = mul_isfun {m1, n1} {m1 * n1, m2 * n2} (pf1, pf2)
  in
  end

prfn
pos_mul_pos_pos
          {m, n : int | 0 < n}
          {p    : int | 0 < p; m * n == p}
          ()
    :<prf> [0 < m] void =
  (* Proof by reductio ad absurdum. *)
  sif m <= 0 then
    case+ 0 of
      | _ =/=> mul_lte_gte_lte {m, n} ()
  else
    ()

extern prfn
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

primplement
array_v_takeout2 {a} {p} {n} {i, j} pf_arr =
  sif i < j then
    let
      prval @(pf1, pf1a) = array_v_split {a} {p} {n} {i} pf_arr
      prval @(pf2, pf3) =
        array_v_split {a} {p + (i * sizeof a)} {n - i} {j - i} pf1a
      prval @(pf_i, pf2a) =
        array_v_uncons {a} {p + (i * sizeof a)} {j - i} pf2
      prval @(pf_j, pf3a) =
        array_v_uncons {a} {p + (j * sizeof a)} {n - j} pf3
    in
      @(pf_i, pf_j,
        lam (pf_i, pf_j) =<lin,prf>
          let
            prval pf3 =
              array_v_cons
                {a} {p + (j * sizeof a)} {n - j - 1} (pf_j, pf3a)
            prval pf2 =
              array_v_cons
                {a} {p + (i * sizeof a)} {j - i - 1} (pf_i, pf2a)
            prval pf1a =
              array_v_unsplit {a} {p + (i * sizeof a)} {j - i, n - j}
                              (pf2, pf3)
            prval pf_arr =
              array_v_unsplit {a} {p} {i, n - i} (pf1, pf1a)
          in
            pf_arr
          end)
    end
  else
    let
      prval @(pf_j, pf_i, fpf_ji) =
        array_v_takeout2 {a} {p} {n} {j, i} pf_arr
    in
      @(pf_i, pf_j,
        lam (pf_i, pf_j) =<lin,prf> fpf_ji (pf_j, pf_i))
    end

implement {a}
ptr2bptr_anchor {p} p =
  let
    extern fn
    ptr2bptr_anchor__ :
      {a : vt@ype}
      {p : addr}
      ptr p -<> bptr (a, p, 0) = "mac#%"
  in
    ptr2bptr_anchor__ {a} {p} p
  end

implement {a}
bptr2ptr {p} {i} bp =
  let
    extern fn
    bptr2ptr__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      bptr (a, p, i) -<>
        ptr (p + (i * sizeof a)) = "mac#%"
  in
    bptr2ptr__ {a} {p} {i} bp
  end

implement {a}
bptr_reanchor {p} {i} bp =
  let
    extern fn
    bptr_reanchor__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      bptr (a, p, i) -<>
        bptr_anchor (a, p + (i * sizeof a)) = "mac#%"
  in
    bptr_reanchor__ {a} {p} {i} bp
  end

implement {a} {tk}
bptr_add_g1uint {p} {i} {j} (bp, j) =
  let
    extern fn
    bptr_add_size__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (bptr (a, p, i), size_t j, size_t (sizeof a)) -<>
        bptr (a, p, i + j) = "mac#%"
  in
    bptr_add_size__ {a} {p} {i} {j} (bp, g1u2u j, sizeof<a>)
  end

implement {a} {tk}
bptr_add_g1int {p} {i} {j} (bp, j) =
  let
    extern fn
    bptr_add_ssize__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (bptr (a, p, i), ssize_t j, size_t (sizeof a)) -<>
        bptr (a, p, i + j) = "mac#%"
  in
    bptr_add_ssize__ {a} {p} {i} {j} (bp, g1i2i j, sizeof<a>)
  end

implement {a} {tk}
bptr_sub_g1uint {p} {i} {j} (bp, j) =
  let
    extern fn
    bptr_sub_size__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (bptr (a, p, i), size_t j, size_t (sizeof a)) -<>
        bptr (a, p, i - j) = "mac#%"
  in
    bptr_sub_size__ {a} {p} {i} {j} (bp, g1u2u j, sizeof<a>)
  end

implement {a} {tk}
bptr_sub_g1int {p} {i} {j} (bp, j) =
  let
    extern fn
    bptr_ssize_sub__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      {j : int}
      (bptr (a, p, i), ssize_t j, size_t (sizeof a)) -<>
        bptr (a, p, i - j) = "mac#%"
  in
    bptr_ssize_sub__ {a} {p} {i} {j} (bp, g1i2i j, sizeof<a>)
  end

implement {a}
bptr_succ {p} {i} bp =
  let
    extern fn
    bptr_succ__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      (bptr (a, p, i), size_t (sizeof a)) -<>
        bptr (a, p, i + 1) = "mac#%"
  in
    bptr_succ__ {a} {p} {i} (bp, sizeof<a>)
  end

implement {a}
bptr_pred {p} {i} bp =
  let
    extern fn
    bptr_pred__ :
      {a : vt@ype}
      {p : addr}
      {i : int}
      (bptr (a, p, i), size_t (sizeof a)) -<>
        bptr (a, p, i - 1) = "mac#%"
  in
    bptr_pred__ {a} {p} {i} (bp, sizeof<a>)
  end

implement {a}
bptr_diff {p} {i, j} (bp_i, bp_j) =
  let
    extern fn
    bptr_diff__ :
      {a    : vt@ype}
      {p    : addr}
      {i, j : int}
      (bptr (a, p, i), bptr (a, p, j), size_t (sizeof a)) -<>
        size_t (i - j) = "mac#%"
  in
    bptr_diff__ {a} {p} {i, j} (bp_i, bp_j, sizeof<a>)
  end

implement {a}
bptr_get (pf_view | bp) =
  ptr_get<a> (pf_view | bptr2ptr bp)

implement {a}
bptr_set (pf_view | bp, x) =
  ptr_set<a> (pf_view | bptr2ptr bp, x)

implement {a}
bptr_exch (pf_view | bp, x) =
  ptr_exch<a> (pf_view | bptr2ptr bp, x)

implement {a}
interchange_bptr_bptr {p} {n} {i, j} (pf_arr | bp_i, bp_j) =
  if bp_i <> bp_j then
    let
      fn {}
      exch (pf_i   : !a @ (p + (i * sizeof a)),
            pf_j   : !a @ (p + (j * sizeof a)) |
            bp_i   : bptr (a, p, i),
            p_j    : ptr (p + (j * sizeof a)))
          :<!wrt> void =
        bptr_exch<a> (pf_i | bp_i, !p_j)

      prval @(pf_i, pf_j, fpf) =
        array_v_takeout2 {a} {p} {n} {i, j} pf_arr
      val p_j = bptr2ptr bp_j
      val () = exch (pf_i, pf_j | bp_i, p_j)
      prval () = pf_arr := fpf (pf_i, pf_j)
    in
    end

implement {a}
subreverse_bptr_bptr {p} {n} {i, j} (pf_arr | bp_i, bp_j) =
  let
    fun
    loop {i, j : int | 0 <= i; i <= j; j <= n}
         .<j - i>.
         (pf_arr : !array_v (a, p, n) |
          bp_i   : bptr (a, p, i),
          bp_j   : bptr (a, p, j))
        :<!wrt> void =
      let
        val bp_i1 = bptr_succ<a> bp_i
      in
        if bp_i1 < bp_j then
          let
            val bp_j1 = bptr_pred<a> bp_j
          in
            interchange_bptr_bptr<a> (pf_arr | bp_i, bp_j1);
            loop (pf_arr | bp_i1, bp_j1)
          end
      end
  in
    loop (pf_arr | bp_i, bp_j)
  end

implement {a}
subcirculate_right_bptr_bptr {p} {n} {i, j}
                             (pf_arr | bp_i, bp_j) =
  if bp_i <> bp_j then
    let
      extern fn                 (* Unsafe memmove. *)
      memmove : (Ptr, Ptr, Size_t) -< !wrt > void = "mac#%"

      prval @(pf_i, pf_j, fpf) =
        array_v_takeout2 {a} {p} {n} {i, j} pf_arr

      val tmp = bptr_get<a> (pf_j | bp_j)

      prval () = lemma_sizeof {a} ()
      prval () = mul_gte_gte_gte {j - i, sizeof a} ()
      val () =
        memmove (bptr2ptr (bptr_succ<a> bp_i),
                 bptr2ptr bp_i,
                 bptr_diff<a> (bp_j, bp_i) * sizeof<a>)

      prval () = $UN.castview2void_at{a?}{a} pf_i
      val () = bptr_set<a> (pf_i | bp_i, tmp)

      prval () = $UN.castview2void_at{a}{a?!} pf_j
      prval () = pf_arr := fpf (pf_i, pf_j)
    in
    end

implement {a}
subcirculate_right_with_gap_bptr_bptr {p} {n} {i, m, gap}
                                      (pf_arr | bp_i, bp_j, gap) =
  if bp_i = bp_j then
    ()
  else if gap = i2sz 1 then
    let
      stadef j = i + (m * gap)
      prval () = mul_gte_gte_gte {m, gap} ()
    in
      subcirculate_right_bptr_bptr {p} {n} {i, j}
                                   (pf_arr | bp_i, bp_j)
    end
  else
    let
      stadef j = i + (m * gap)

      prval () = mul_gte_gte_gte {m, gap} ()
      prval () = prop_verify {i <= j} ()

      prval @(pf_before_i, pf) =
        array_v_split {a} {p} {n} {i} pf_arr
      prval @(pf_ij, pf_after_j) =
        array_v_split {a} {p + (i * sizeof a)} {n - i} {j - i + 1} pf

      prval @(pf_arr1, pf_j) = array_v_unextend pf_ij
      val jth_element = bptr_get<a> (pf_j | bp_j)

      fun
      loop {r, k : int | 0 <= r; i <= k; k <= j; k == i + (r * gap)}
           .<k - i>.
           (pf_arr1 : array_v (a, p + (i * sizeof a), k - i),
            pf_k    : a?! @ (p + (k * sizeof a)),
            pf_arr2 : array_v (a, p + (k * sizeof a) + sizeof a,
                               j - k) |
            bp_k    : bptr (a, p, k))
          :<!wrt> @(a?! @ (p + (i * sizeof a)),
                    array_v (a, p + (i * sizeof a) + sizeof a,
                             j - i) | ) =
        if bp_i = bp_k then
          let
            prval () = array_v_unnil pf_arr1
            prval () = lemma_mul_isfun {i, sizeof a} {k, sizeof a} ()
          in
            @(pf_k, pf_arr2 | )
          end
        else
          let
            prval () = prop_verify {1 <= k - i} ()
            prval () = prop_verify {k - i == r * gap} ()

            prval () = pos_mul_pos_pos {r, gap} {r * gap} ()
            prval () = prop_verify {1 <= r} ()

            prval () = mul_pos_pos_pos (mul_make {r, gap} ())
            prval () = prop_verify {gap <= k - i} ()

            val bp_k1 = bptr_sub<a> (bp_k, gap)
            prval @(pf_arr1, pf_gap) =
              array_v_split {a} {p + (i * sizeof a)} {k - i}
                            {k - i - gap}
                            pf_arr1
            prval @(pf_k1, pf_gap) = array_v_uncons pf_gap
            val tmp = bptr_get<a> (pf_k1 | bp_k1)
            val () = bptr_set<a> (pf_k | bp_k, tmp)
            prval pf_arr2 = array_v_cons (pf_k, pf_arr2)
            prval pf_arr2 = array_v_unsplit (pf_gap, pf_arr2)
          in
            loop {r - 1, k - gap} (pf_arr1, pf_k1, pf_arr2 | bp_k1)
          end

      prval () = lemma_sizeof {a} ()

      prval pf_arr2 =
        array_v_nil {a} {p + (j * sizeof a) + sizeof a} ()
      val @(pf_i, pf_arr2 | ) =
        loop {m, j} (pf_arr1, pf_j, pf_arr2 | bp_j)

      val () = bptr_set<a> (pf_i | bp_i, jth_element)

      prval pf_ij = array_v_cons (pf_i, pf_arr2)
      prval pf = array_v_unsplit (pf_ij, pf_after_j)
      prval () = pf_arr := array_v_unsplit (pf_before_i, pf)
    in
    end

implement {a}
copy_bptr_bptr_size {dst} {src} {n}
                    (pf_dst, pf_src | bp_dst, bp_src, n) =
  let
    extern fn                   (* Unsafe memcpy. *)
    memcpy : (Ptr, Ptr, Size_t) -< !wrt > void = "mac#%"

    prval () = lemma_sizeof {a} ()
    prval () = lemma_array_v_param pf_dst
    prval () = mul_gte_gte_gte {sizeof a, n} ()

    val () = memcpy (bptr2ptr bp_dst, bptr2ptr bp_src,
                     sizeof<a> * n)

    prval () = $UN.castview2void {array_v (a, dst, n)}
                                 {array_v (a?, dst, n)}
                                 pf_dst
    prval () = $UN.castview2void {array_v (a?!, src, n)}
                                 {array_v (a, src, n)}
                                 pf_src
  in
  end

implement {a}
copy_bptr_bptr_bptr {dst} {src} {n}
                    (pf_dst, pf_src | bp_dst, bp_src, bp_n) =
  let
    prval () = lemma_array_v_param pf_dst
  in
    copy_bptr_bptr_size
      {dst} {src} {n}
      (pf_dst, pf_src | bp_dst, bp_src, bp_n - bp_src)
  end

implement {a}
move_left_bptr_bptr_size {dst} {i} {n}
                         (pf_dst, pf_src | bp_dst, bp_src, n) =
  let
    extern fn                   (* Unsafe memmove. *)
    memmove : (Ptr, Ptr, Size_t) -< !wrt > void = "mac#%"

    prval () = lemma_sizeof {a} ()
    prval () = lemma_g1uint_param n
    prval () = mul_gte_gte_gte {sizeof a, n} ()

    val () = memmove (bptr2ptr bp_dst, bptr2ptr bp_src,
                      sizeof<a> * n)

    prval () = $UN.castview2void {array_v (a, dst, n)}
                                 {array_v (a?, dst, i)}
                                 pf_dst
    prval () =
      $UN.castview2void {array_v (a?!, dst + (n * sizeof a), i)}
                        {array_v (a, dst + (i * sizeof a), n)}
                        pf_src
  in
  end

implement {a}
move_left_bptr_bptr_bptr {dst} {i} {n}
                         (pf_dst, pf_src |
                          bp_dst, bp_src, bp_n) =
  let
    prval () = lemma_array_v_param pf_dst
  in
    move_left_bptr_bptr_size
      {dst} {i} {n}
      (pf_dst, pf_src | bp_dst, bp_src, bp_n - bp_src)
  end

implement {a}
move_right_bptr_bptr_size {src} {i} {n}
                          (pf_dst, pf_src | bp_dst, bp_src, n) =
  let
    extern fn                   (* Unsafe memmove. *)
    memmove : (Ptr, Ptr, Size_t) -< !wrt > void = "mac#%"

    prval () = lemma_sizeof {a} ()
    prval () = lemma_g1uint_param n
    prval () = mul_gte_gte_gte {sizeof a, i} ()
    prval () = mul_gte_gte_gte {sizeof a, n} ()

    val () = memmove (bptr2ptr bp_dst, bptr2ptr bp_src,
                      sizeof<a> * n)

    prval () =
      $UN.castview2void {array_v (a, src + (i * sizeof a), n)}
                        {array_v (a?, src + (n * sizeof a), i)}
                        pf_dst
    prval () = $UN.castview2void {array_v (a?!, src, i)}
                                 {array_v (a, src, n)}
                                 pf_src
  in
  end

implement {a}
move_right_bptr_bptr_bptr {src} {i} {n}
                          (pf_dst, pf_src |
                           bp_dst, bp_src, bp_n) =
  let
    prval () = lemma_array_v_param pf_dst
  in
    move_right_bptr_bptr_size
      {src} {i} {n}
      (pf_dst, pf_src | bp_dst, bp_src, bp_n - bp_src)
  end

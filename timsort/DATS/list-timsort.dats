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

staload "timsort/SATS/list-timsort.sats"

staload "timsort/SATS/COMMON/timsort-common.sats"
staload _ = "timsort/DATS/COMMON/timsort-common.dats"

#define STK_MAX_THRESHOLD 64   (* The bitsize of a size_t on AMD64. *)

#define NIL list_vt_nil ()
#define ::  list_vt_cons

macdef orelse1 (a, b) = (if ,(a) then true else ,(b))
infix ( || ) |||
macdef ||| = orelse1

macdef andalso1 (a, b) = (if ,(a) then ,(b) else false)
infix ( && ) &&&
macdef &&& = andalso1

(*------------------------------------------------------------------*)

implement {a}
list_vt_timsort$lt (x, y) =
  list_vt_timsort$cmp<a> (x, y) < 0

implement {a}
list_vt_timsort$cmp (x, y) =
  (* This default is the same as for list_vt_mergesort$cmp in the
     prelude. *)
  gcompare_ref_ref<a> (x, y)

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
list_vt_insertion_sort_with_some_of_it_presorted :
  {m, n : int}
  (list_vt (a, m),
   list_vt (a, n)) -< !wrt >
    list_vt (a, m + n)

extern fn {a : vt@ype}
list_vt_insertion_sort_without_any_of_it_presorted :
  {n : int}
  list_vt (a, n) -< !wrt >
    list_vt (a, n)

extern fn {a : vt@ype}
list_vt_insertion_sort$lt :
  (&a, &a) -<> bool

overload list_vt_insertion_sort with
  list_vt_insertion_sort_with_some_of_it_presorted
overload list_vt_insertion_sort with
  list_vt_insertion_sort_without_any_of_it_presorted

implement {a}
list_vt_insertion_sort_with_some_of_it_presorted
                    {m, n} (lst, presorted) =
  let
    prval () = lemma_list_vt_param lst
    prval () = lemma_list_vt_param presorted

    fun
    insert {u       : nat}
           {p_xnode : addr}
           {p_x     : addr}
           {p_xs    : addr}
           .<u>.
           (pf_x  : a @ p_x,
            pf_xs : list_vt (a, 0)? @ p_xs |
            dst   : &list_vt (a, u) >> list_vt (a, u + 1),
            (* list_vt_cons_unfold is a viewtype created by the
               unfolding of a list_vt_cons (our :: operator). *)
            xnode : list_vt_cons_unfold (p_xnode, p_x, p_xs),
            p_x   : ptr p_x,
            p_xs  : ptr p_xs)
        :<!wrt> void =

      (*
        dst is some tail of the current destination list; xnode is a
        viewtype for the current node in the source list.

        p_x points to the node's CAR.

        p_xs points to the node's CDR.
      *)
      case+ dst of
      | @ (y :: ys) =>
        if ~list_vt_insertion_sort$lt<a> (!p_x, y) then
          let                 (* Move to the next destination node. *)
            val () = insert (pf_x, pf_xs | ys, xnode, p_x, p_xs)
            prval () = fold@ dst
          in
          end
        else
          let                   (* Insert xnode here. *)
            prval () = fold@ dst
            val () = !p_xs := dst
            val () = dst := xnode
            prval () = fold@ dst
          in
          end
      | ~ NIL =>
        let                     (* Put xnode at the end. *)
          val () = dst := xnode
          val () = !p_xs := NIL
          prval () = fold@ dst
        in
        end

    fun                         (* Create a sorted list. *)
    loop {u : int | n <= u; u <= n + m}
         .<n + m - u>.
         (dst : &list_vt (a, u) >> list_vt (a, n + m),
          src : list_vt (a, n + m - u))
        :<!wrt> void =
      case+ src of
      | @ (x :: xs) =>
        let
          val tail = xs
        in
          insert (view@ x, view@ xs | dst, src, addr@ x, addr@ xs);
          loop (dst, tail)
        end
      | ~ NIL => ()             (* We are done. *)

    var dst : [u : int | n <= u] list_vt (a, u) = presorted
  in
    loop (dst, lst);
    dst
  end

implement {a}
list_vt_insertion_sort_without_any_of_it_presorted lst =
  list_vt_insertion_sort_with_some_of_it_presorted<a> (lst, NIL)

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
split_at_pair_after_first :
  {n : int | 2 <= n}
  list_vt (a, n) -< !wrt >
    [m : int | 2 <= m; m <= n]
    @(list_vt (a, m),
      list_vt (a, n - m),
      int m)

extern fn {a : vt@ype}
split_at_pair_after_first$here :
  (&a, &a) -<> bool

implement {a}
split_at_pair_after_first {n} lst =
  let
    fun
    loop {m0 : int | 2 <= m0; m0 <= n}
         .<n - m0>.
         (lst1a : &list_vt (a, n - m0) >> list_vt (a, m - m0),
          lst2  : &(List_vt a)? >> list_vt (a, n - m),
          prev  : &a,
          m0    : int m0,
          m     : &int? >> int m)
        :<!wrt> #[m : int | m0 <= m; m <= n]
                void =
      case+ lst1a of
      | NIL =>
        begin
          lst2 := NIL;
          m := m0
        end
      | @ (next :: rest) =>
        let
          val done = split_at_pair_after_first$here<a> (prev, next)
        in
          if done then
            let
              prval () = fold@ lst1a
            in
              lst2 := lst1a;
              lst1a := NIL;
              m := m0
            end
          else
            let
              val () = loop (rest, lst2, next, m0 + 1, m)
              prval () = fold@ lst1a
            in
            end
        end

    var lst1 = lst
    var lst2 : List_vt a
    var m : int

    (* It is assumed that the second list element is not less than the
       first. (We do not prove the result is monotonically
       non-descending, anyway, so I will not bother to prove or assert
       this precondition. We will unit-test the routine.) *)

    val+ @ (_first :: rest1) = lst1
    val+ @ (second :: rest2) = rest1
    val () = loop (rest2, lst2, second, 2, m)
    prval () = fold@ rest1
    prval () = fold@ lst1
  in
    @(lst1, lst2, m)
  end

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
split_after_nondecreasing_run :
  {n : int | 2 <= n}
  list_vt (a, n) -< !wrt >
    [m : int | 2 <= m; m <= n]
    @(list_vt (a, m),
      list_vt (a, n - m),
      int m)

implement {a}
split_after_nondecreasing_run {n} lst =
  let
    implement
    split_at_pair_after_first$here<a> (prev, next) =
      list_vt_timsort$lt<a> (next, prev)
  in
    split_at_pair_after_first<a> {n} lst
  end

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
split_after_decreasing_run :
  {n : int | 2 <= n}
  list_vt (a, n) -< !wrt >
    [m : int | 2 <= m; m <= n]
    @(list_vt (a, m),
      list_vt (a, n - m),
      int m)

implement {a}
split_after_decreasing_run {n} lst =
  let
    implement
    split_at_pair_after_first$here<a> (prev, next) =
      ~list_vt_timsort$lt<a> (next, prev)
  in
    split_at_pair_after_first {n} lst
  end

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
list_vt_split_at_most :
  {n : int}
  {i : nat}
  (list_vt (a, n),
   int i) -< !wrt >
    [m : nat | m == min (n, i)]
    @(list_vt (a, m),
      list_vt (a, n - m),
      int m)

implement {a}
list_vt_split_at_most {n} {i} (lst, i) =
  let
    prval () = lemma_list_vt_param lst
    prval () = prop_verify {0 <= min (n, i)} ()

    fun
    loop {m0 : nat | m0 <= min (n, i)}
         .<n - m0>.
         (lst1a : &list_vt (a, n - m0) >> list_vt (a, m - m0),
          lst2  : &(List_vt a)? >> list_vt (a, n - m),
          m0    : int m0,
          m     : &int? >> int m)
        :<!wrt> #[m : int | m == min (n, i)]
                void =
      if (m0 = i) + (iseqz<a> lst1a) then
        begin
          lst2 := lst1a;
          lst1a := NIL;
          m := m0
        end
      else
        let
          val+ @ (_ :: rest) = lst1a
          val () = loop (rest, lst2, m0 + 1, m)
          prval () = fold@ lst1a
        in
        end

    var lst1 = lst
    var lst2 : List_vt a
    var m : int

    val () = loop (lst1, lst2, 0, m)
  in
    @(lst1, lst2, m)
  end

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
provide_a_nondecreasing_run :
  {n      : int | 2 <= n}
  {minrun : int | 2 <= minrun}
  (list_vt (a, n),
   int minrun) -< !wrt >
    [m : int | min (n, minrun) <= m; m <= n]
    @(list_vt (a, m),
      list_vt (a, n - m),
      int m)

implement {a}
provide_a_nondecreasing_run {n} {minrun} (lst, minrun) =
  let
    val+ @ (first :: rest1) = lst
    val+ @ (second :: rest2) = rest1
    val nondecreasing = ~list_vt_timsort$lt<a> (second, first)
    prval () = fold@ rest1
    prval () = fold@ lst
  in
    if nondecreasing then
      let                       (* A nondecreasing run. *)
        val @(lst1, lst2, m) = split_after_nondecreasing_run<a> lst
      in
        if (minrun <= m) + (iseqz<a> lst2) then
          @(lst1, lst2, m)
        else
          let
            implement
            list_vt_insertion_sort$lt<a> (x, y) =
              list_vt_timsort$lt<a> (x, y)

            val i = minrun - m
            val @(lst1a, lst2, j) = list_vt_split_at_most<a> (lst2, i)
            val lst1 = list_vt_insertion_sort<a> (lst1a, lst1)
          in
            @(lst1, lst2, m + j)
          end
      end
    else
      let                       (* A decreasing run. *)
        val @(lst1, lst2, m) = split_after_decreasing_run<a> lst
      in
        if (minrun <= m) + (iseqz<a> lst2) then
          @(reverse<a> lst1, lst2, m) (* Reverse the run. *)
        else
          let
            (* The following implementation of
               list_vt_insertion_sort$lt will give us a nonincreasing
               run with the orders of ‘equal’ entries reversed. *)
            implement
            list_vt_insertion_sort$lt<a> (x, y) =
              ~list_vt_timsort$lt<a> (x, y)

            val i = minrun - m
            val @(lst1a, lst2, j) = list_vt_split_at_most<a> (lst2, i)
            val lst1 = list_vt_insertion_sort<a> (lst1a, lst1)
          in
            @(reverse<a> lst1, lst2, m + j) (* Reverse the run. *)
          end
      end
  end

(*------------------------------------------------------------------*)

extern fn {a : vt@ype}
merge_two_nondecreasing_runs :
  {m, n : int}
  (list_vt (a, m),
   list_vt (a, n)) -< !wrt >
    list_vt (a, m + n)

implement {a}
merge_two_nondecreasing_runs (lst1, lst2) =
  let
    fun
    loop {m, n : nat}
         .<m + n>.
         (lst_m  : list_vt (a, m),
          lst_n  : list_vt (a, n),
          result : &List_vt a? >> list_vt (a, m + n))
        :<!wrt> void =
      case+ lst_m of
      | ~ NIL => result := lst_n
      | @ (x :: rest_m) =>
        begin
          case+ lst_n of
          | ~ NIL =>
            let
              prval () = fold@ lst_m
            in
              result := lst_m
            end
          | @ (y :: rest_n) =>
            if ~list_vt_timsort$lt<a> (y, x) then
              let
                prval () = fold@ lst_n
                val () = result := lst_m
                val () = loop (rest_m, lst_n, rest_m)
                prval () = fold@ result
              in
              end
            else
              let
                prval () = fold@ lst_m
                val () = result := lst_n
                val () = loop (lst_m, rest_n, rest_n)
                prval () = fold@ result
              in
              end
        end

    prval () = lemma_list_vt_param lst1
    prval () = lemma_list_vt_param lst2

    var result : List_vt a
  in
    loop (lst1, lst2, result);
    result
  end

(*------------------------------------------------------------------*)

typedef stk_entry_t (index : int, size : int, power : int) =
  [0 <= index; 1 <= size]
  @{
    p_sublist = ptr,    (* The address of the sublist’s first node. *)
    index = int index,  (* Where the sublist begins. *)
    size = int size,    (* The size of the sublist. *)
    power = int power   (* The node power, if it has been computed. *)
  }
typedef stk_entry_t =
  [index, size, power : int]
  stk_entry_t (index, size, power)

vtypedef stk_vt (p          : addr,
                 depth      : int,
                 stk_max    : int) =
  @{
    pf         = array_v (stk_entry_t, p, stk_max) |
    p          = ptr p,
    depth      = int depth,
    stk_max    = int stk_max
  }

fn {a : vt@ype}
stk_entry2list
          {index : nat}
          {size  : pos}
          {power : int}
          (entry : stk_entry_t (index, size, power))
    :<> list_vt (a, size) =
  $UN.castvwtp0{list_vt (a, size)} (entry.p_sublist)

fn {}
stk_vt_make
          {p       : addr}
          {stk_max : int}
          (pf      : array_v (stk_entry_t, p, stk_max) |
           p       : ptr p,
           stk_max : size_t stk_max)
    :<> stk_vt (p, 0, stk_max) =
  @{
    pf = pf |
    p = p,
    depth = 0,
    stk_max = sz2i stk_max
  }

fn {}
stk_vt_depth
          {p_stk   : addr}
          {stk_max : int}
          {depth   : int}
          (stk : &stk_vt (p_stk, depth, stk_max))
    :<> int depth =
  stk.depth

fn {a : vt@ype}
stk_vt_push
          {index   : nat}
          {size    : pos}
          {power   : int}
          {p_stk   : addr}
          {stk_max : int}
          {depth   : nat}
          (sublist : list_vt (a, size),
           index   : int index,
           size    : int size,
           power   : int power,
           stk     : &stk_vt (p_stk, depth, stk_max)
                        >> stk_vt (p_stk, depth + 1, stk_max))
    :<!wrt> void =
  let
    macdef storage = !(stk.p)
    val () = $effmask_exn assertloc ((stk.depth) < (stk.stk_max))
  in
    storage[stk.depth] :=
      @{
        p_sublist = $UN.castvwtp0{ptr} sublist,
        index = index,
        size = size,
        power = power
      };
    stk.depth := succ (stk.depth)
  end

fn {}
stk_vt_peek
          {p_stk     : addr}
          {stk_max   : int}
          {depth     : int}
          {entry_num : nat | entry_num < depth}
          (stk       : &stk_vt (p_stk, depth, stk_max),
           entry_num : int entry_num)
    :<> [index, size, power : int | 0 <= index; 1 <= size]
        stk_entry_t (index, size, power) =
  let
    macdef storage = !(stk.p)
    val () = $effmask_exn assertloc ((stk.depth) <= (stk.stk_max))
  in
    storage[pred ((stk.depth) - entry_num)]
  end

fn {}
stk_vt_drop
          {p_stk   : addr}
          {stk_max : int}
          {depth   : pos}
          (stk     : &stk_vt (p_stk, depth, stk_max)
                      >> stk_vt (p_stk, depth - 1, stk_max))
    :<!wrt> void =
  stk.depth := pred (stk.depth)

fn {}
stk_vt_pop
          {p_stk   : addr}
          {stk_max : int}
          {depth   : int | 1 <= depth}
          (stk     : &stk_vt (p_stk, depth, stk_max)
                      >> stk_vt (p_stk, depth - 1, stk_max))
    :<!wrt> #[index, size, power : int | 0 <= index; 1 <= size]
            stk_entry_t (index, size, power) =
  let
    val entry = stk_vt_peek (stk, 0)
  in
    stk_vt_drop stk;
    entry
  end

fn {a : vt@ype}
stk_vt_overwrite
          {index     : nat}
          {size      : pos}
          {power     : int}
          {p_stk     : addr}
          {stk_max   : int}
          {depth     : int}
          {entry_num : nat | entry_num < depth}
          (sublist   : list_vt (a, size),
           index     : int index,
           size      : int size,
           power     : int power,
           stk       : &stk_vt (p_stk, depth, stk_max),
           entry_num : int entry_num)
    :<!wrt> void =
  let
    macdef storage = !(stk.p)
    val () = $effmask_exn assertloc ((stk.depth) <= (stk.stk_max))
  in
    storage[pred ((stk.depth) - entry_num)] :=
      @{
        p_sublist = $UN.castvwtp0{ptr} sublist,
        index = index,
        size = size,
        power = power
      }
  end

fn {}
stk_vt_overwrite_power
          {power     : int}
          {p_stk     : addr}
          {stk_max   : int}
          {depth     : int}
          {entry_num : nat | entry_num < depth}
          (power     : int power,
           stk       : &stk_vt (p_stk, depth, stk_max),
           entry_num : int entry_num)
    :<!wrt> void =
  let
    macdef storage = !(stk.p)
    val () = $effmask_exn assertloc ((stk.depth) <= (stk.stk_max))

    val @{
          p_sublist = p_sublist,
          index = index,
          size = size,
          power = _
        } = storage[pred ((stk.depth) - entry_num)]
  in
    storage[pred ((stk.depth) - entry_num)] :=
      @{
        p_sublist = p_sublist,
        index = index,
        size = size,
        power = power
      }
  end

(*------------------------------------------------------------------*)
(* Powersort strategy.                                              *)

extern fn {a : vt@ype}
include_new_run
          {n       : int}
          {index   : nat}
          {size    : pos | index + size <= n}
          {p_stk   : addr}
          {stk_max : int}
          {depth0  : nat}
          (n       : int n,
           run     : list_vt (a, size),
           index   : int index,
           size    : int size,
           stk     : &stk_vt (p_stk, depth0, stk_max)
                      >> stk_vt (p_stk, depth1, stk_max))
    :<!wrt> #[depth1 : pos | depth1 <= depth0 + 1]
            void

extern fn {a : vt@ype}
merge_remaining_runs
          {n       : pos}
          {p_stk   : addr}
          {stk_max : int}
          {depth0  : pos}
          (n       : int n,
           stk     : &stk_vt (p_stk, depth0, stk_max)
                      >> stk_vt (p_stk, 0, stk_max))
    :<!wrt> list_vt (a, n)

#define ARBITRARY_POWER ~1234

implement {a}
include_new_run {n} {index} {size} (n, run, index, size, stk) =
  if stk_vt_depth stk = 0 then
    stk_vt_push (run, index, size, ARBITRARY_POWER, stk)
  else
    let
      val [index0, size0, _power : int]
          @{
            p_sublist = _,
            index = index0,
            size = size0,
            power = _
          } = stk_vt_peek (stk, 0)
      prval () = prop_verify {0 <= index0} ()
      prval () = prop_verify {1 <= size0} ()

      val () = $effmask_exn assertloc (index0 + size0 = index)
      prval () = prop_verify {index0 + size0 + size <= n} ()

      val power = nodepower (i2sz n, i2sz index0, i2sz size0,
                             i2sz size)

      fun
      merge_sublists
                {p_stk   : addr}
                {stk_max : int}
                {depth1  : pos}
                .<depth1>.
                (stk : &stk_vt (p_stk, depth1, stk_max)
                        >> stk_vt (p_stk, depth2, stk_max))
          :<!wrt> #[depth2 : pos | depth2 <= depth1]
                  void =
        if stk_vt_depth stk = 1 then
          ()
        else if ((stk_vt_peek (stk, 1)).power) <= power then
          ()
        else
          let
            val peek0 = stk_vt_peek (stk, 0)
            and peek1 = stk_vt_peek (stk, 1)

            val @{
                  p_sublist = _,
                  index = index0,
                  size = size0,
                  power = _
                } = peek0
            and @{
                  p_sublist = _,
                  index = index1,
                  size = size1,
                  power = _
                } = peek1
            and sublist0 = stk_entry2list peek0
            and sublist1 = stk_entry2list peek1

            prval [index0 : int] EQINT () = eqint_make_gint index0
            prval [size0 : int] EQINT () = eqint_make_gint size0
            prval [index1 : int] EQINT () = eqint_make_gint index1
            prval [size1 : int] EQINT () = eqint_make_gint size1

            val () = $effmask_exn assertloc (index1 + size1 = index0)
            val () = $effmask_exn assertloc (index0 + size0 = index)
            prval () =
              prop_verify {index1 + size1 + size0 + size <= n} ()

            val merger =
              merge_two_nondecreasing_runs<a> (sublist1, sublist0)
          in
            stk_vt_overwrite (merger, index1, size1 + size0,
                              ARBITRARY_POWER, stk, 1);
            stk_vt_drop stk;
            merge_sublists stk
          end
    in
      merge_sublists stk;
      stk_vt_overwrite_power (power, stk, 0);
      stk_vt_push (run, index, size, ARBITRARY_POWER, stk)
    end

implement {a}
merge_remaining_runs {n} (n, stk) =
  let
    fn
    merge_1_with_0
              {p_stk   : addr}
              {stk_max : int}
              {depth   : int | 2 <= depth}
              (stk     : &stk_vt (p_stk, depth, stk_max)
                          >> stk_vt (p_stk, depth - 1, stk_max))
        :<!wrt> void =
      let
        val entry0 = stk_vt_pop stk
        val entry1 = stk_vt_peek (stk, 0)
        val @{
              p_sublist = _,
              index = index0,
              size = size0,
              power = _
            } = entry0
        and @{
              p_sublist = _,
              index = index1,
              size = size1,
              power = _
            } = entry1
        and sublist0 = stk_entry2list entry0
        and sublist1 = stk_entry2list entry1

        val () = $effmask_exn assertloc (index1 + size1 = index0)
        val () = $effmask_exn assertloc (index0 + size0 = n)

        val merger =
          merge_two_nondecreasing_runs<a> (sublist1, sublist0)
      in
        stk_vt_overwrite (merger, index1, size1 + size0,
                          ARBITRARY_POWER, stk, 0)
      end

    fn
    merge_2_with_1
              {p_stk   : addr}
              {stk_max : int}
              {depth   : int | 3 <= depth}
              (stk     : &stk_vt (p_stk, depth, stk_max)
                          >> stk_vt (p_stk, depth - 1, stk_max))
        :<!wrt> void =
      let
        val entry0 = stk_vt_pop stk
        val entry1 = stk_vt_pop stk
        val entry2 = stk_vt_pop stk

        val @{
              p_sublist = _,
              index = index0,
              size = size0,
              power = _
            } = entry0
        and @{
              p_sublist = _,
              index = index1,
              size = size1,
              power = _
            } = entry1
        and @{
              p_sublist = _,
              index = index2,
              size = size2,
              power = _
            } = entry2
        and sublist0 = stk_entry2list entry0
        and sublist1 = stk_entry2list entry1
        and sublist2 = stk_entry2list entry2

        val () = $effmask_exn assertloc (index2 + size2 = index1)
        val () = $effmask_exn assertloc (index1 + size1 = index0)
        val () = $effmask_exn assertloc (index0 + size0 = n)

        val merger =
          merge_two_nondecreasing_runs<a> (sublist2, sublist1)
      in
        stk_vt_push (merger, index2, size2 + size1,
                     ARBITRARY_POWER, stk);
        stk_vt_push (sublist0, index0, size0, ARBITRARY_POWER, stk)
      end

    fun
    loop {p_stk   : addr}
         {stk_max : int}
         {depth   : pos}
         .<depth>.
         (stk : &stk_vt (p_stk, depth, stk_max)
                  >> stk_vt (p_stk, 0, stk_max))
        :<!wrt> list_vt (a, n) =
      if stk_vt_depth stk = 1 then
        let
          val entry0 = stk_vt_pop stk
          val @{
                p_sublist = _,
                index = index0,
                size = size0,
                power = _
              } = entry0
          and sorted_list = stk_entry2list entry0

          val () = $effmask_exn assertloc (index0 = 0)
          val () = $effmask_exn assertloc (size0 = n)
        in
          sorted_list
        end
      else if stk_vt_depth stk = 2 then
        begin
          merge_1_with_0 stk;
          loop stk
        end
      else if ((stk_vt_peek (stk, 0)).size)
                  <= ((stk_vt_peek (stk, 2)).size) then
        begin
          merge_1_with_0 stk;
          loop stk
        end
      else
        begin
          merge_2_with_1 stk;
          loop stk
        end
  in
    loop stk
  end

(*------------------------------------------------------------------*)

fn {a : vt@ype}
timsort_main
          {n       : nat}
          {p_stk   : addr}
          {stk_max : pos}
          (lst     : list_vt (a, n),
           n       : int n,
           stk     : &stk_vt (p_stk, 0, stk_max))
    :<!wrt> list_vt (a, n) =
  if n <= 1 then
    lst
  else
    let
      val minrun = sz2i (minimum_run_length (i2sz n))
      prval [minrun : int] EQINT () = eqint_make_gint minrun
      prval () = prop_verify {2 <= minrun} ()

      fun
      loop {i      : nat | i <= n}
           {depth0 : nat}
           .<n - i>.
           (lst : list_vt (a, n - i),
            i   : int i,
            stk : &stk_vt (p_stk, depth0, stk_max)
                    >> stk_vt (p_stk, depth1, stk_max))
          :<!wrt> #[depth1 : pos]
                  void =
        if i = n then
          let                 (* All done. *)
            val+ ~ NIL = lst
          in
            $effmask_exn assertloc (0 < stk_vt_depth stk)
          end
        else if i = pred n then
          begin               (* A single last element. *)
            include_new_run<a> (n, lst, pred n, 1, stk);
            loop (NIL, n, stk)
          end
        else
          let                 (* A run. *)
            val @(run, rest, runlen) =
              provide_a_nondecreasing_run<a> (lst, minrun)
          in
            include_new_run<a> (n, run, i, runlen, stk);
            loop (rest, i + runlen, stk)
          end
    in
      loop (lst, 0, stk);
      merge_remaining_runs<a> (n, stk)
    end

implement {a}
list_vt_timsort {n} lst =
  let
    prval () = lemma_list_vt_param lst

    val n = length lst
    prval () = prop_verify {0 <= n} ()

    fn
    sort_main {p_stk   : addr}
              {stk_max : pos}
              (lst     : list_vt (a, n),
               stk     : &stk_vt (p_stk, 0, stk_max))
        :<!wrt> list_vt (a, n) =
      timsort_main<a> (lst, n, stk)
  in
    if (char_bit () * sizeof<size_t> <= i2sz STK_MAX_THRESHOLD)
          ||| (iseqz (n >> STK_MAX_THRESHOLD)) then
      let                       (* Put stk on the system stack. *)
        var stk_storage =
          @[stk_entry_t][STK_MAX_THRESHOLD]
            (@{
               p_sublist = the_null_ptr,
               index = 0,
               size = 1,
               power = 0
             })
        var stk = stk_vt_make (view@ stk_storage |
                               addr@ stk_storage,
                               i2sz STK_MAX_THRESHOLD)
        val sorted_list = sort_main (lst, stk)
        prval () = view@ stk_storage := stk.pf
      in
        sorted_list
      end
    else
      let                       (* Put stk in the heap. *)
        val bitsz = char_bit () * sizeof<size_t>
        val () = $effmask_exn assertloc (i2sz 1 <= bitsz)
        val @(pf_stk_storage, pfgc_stk_storage | p_stk_storage) =
          array_ptr_alloc<stk_entry_t> bitsz
        val entry =
          @{
            p_sublist = the_null_ptr,
            index = 0,
            size = 1,
            power = 0
          }
        val () = array_initize_elt<stk_entry_t> (!p_stk_storage,
                                                 bitsz, entry)
        var stk = stk_vt_make (pf_stk_storage | p_stk_storage, bitsz)
        val sorted_list = sort_main (lst, stk)
        val () = pf_stk_storage := stk.pf
        val () = array_ptr_free (pf_stk_storage, pfgc_stk_storage |
                                 p_stk_storage)
      in
        sorted_list
      end
  end

(*------------------------------------------------------------------*)

implement {a}
list_timsort$lt (x, y) =
  list_timsort$cmp<a> (x, y) < 0

implement {a}
list_timsort$cmp (x, y) =
  (* This default is the same as for list_mergesort$cmp in the
     prelude. *)
  gcompare_val_val<a> (x, y)

implement {a}
list_timsort lst =
  let
    implement
    list_vt_timsort$lt<a> (x, y) =
      list_timsort$lt<a> (x, y)
  in
    list_vt_timsort<a> (list_copy<a> lst)
  end

(*------------------------------------------------------------------*)

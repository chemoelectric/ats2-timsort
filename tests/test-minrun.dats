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

(* Unit testing of the minimum run length calculation. *)

#include "timsort/DATS/COMMON/timsort-common.dats"

fn
test_small () : void =
  let
    var n : [n : nat | n <= 64] size_t n
  in
    for (n := i2sz 0; n <> i2sz 64; n := succ n)
      let
        val minrun = minimum_run_length n
      in
        assertloc (minrun = n)
      end
  end

fn
test_powers_of_two () : void =
  let
    var n : [n : pos] size_t n
  in
    for (n := i2sz 64; n <> i2sz 0x1000000; n := n + n)
      let
        val minrun = minimum_run_length n
      in
        assertloc (minrun = i2sz 32)
      end
  end

implement
main () =
  begin
    test_small ();
    test_powers_of_two ();
    assertloc (minimum_run_length (i2sz 35 * i2sz 1024) = i2sz 35);
    assertloc (minimum_run_length (i2sz 63 * i2sz 512) = i2sz 63);
    assertloc (minimum_run_length (pred (i2sz 63 * i2sz 512)) = i2sz 63);
    assertloc (minimum_run_length (succ (i2sz 63 * i2sz 512)) = i2sz 64);
    assertloc (minimum_run_length (succ (i2sz 35 * i2sz 512)) = i2sz 36);
    assertloc (minimum_run_length (succ (i2sz 47 * i2sz 2)) = i2sz 48);
    0
  end

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

(*------------------------------------------------------------------*)

fn
g0uint_is_even_size :
  size_t -<> bool = "mac#%"

fn
g0uint_is_odd_size :
  size_t -<> bool = "mac#%"

fn
g1uint_is_even_size :
  {n : int}
  size_t n -<> bool (n mod 2 == 0) = "mac#%"

fn
g1uint_is_odd_size :
  {n : int}
  size_t n -<> bool (n mod 2 == 1) = "mac#%"

(*------------------------------------------------------------------*)

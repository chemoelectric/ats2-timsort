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

fn {a : vt@ype}
array_timsort :
  {n     : int}
  {arrsz : int | n <= arrsz}
  (&array (a, arrsz),
   size_t n) -< !wrt >
    void

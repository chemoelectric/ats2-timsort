#
# Copyright © 2022 Barry Schwartz
#
# This program is free software: you can redistribute it and/or
# modify it under the terms of the GNU General Public License, as
# published by the Free Software Foundation, either version 3 of the
# License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received copies of the GNU General Public License
# along with this program. If not, see
# <https://www.gnu.org/licenses/>.
#

#--------------------------------------------------------------------------

AC_PREREQ([2.71])
AC_INIT([ats2-timsort],[1.0.0],[],[ats2-timsort],[])

AC_CONFIG_SRCDIR([timsort/SATS/array-timsort.sats])

AC_CONFIG_MACRO_DIR([m4])
AC_CONFIG_AUX_DIR([build-aux])
AC_CANONICAL_BUILD                 dnl On what platform are we compiling?
AC_CANONICAL_HOST                  dnl For what platform are we compiling?
AC_USE_SYSTEM_EXTENSIONS           dnl Define such macros as _GNU_SOURCE.

AM_INIT_AUTOMAKE
AM_SILENT_RULES
AM_MAINTAINER_MODE
LT_INIT

AC_ARG_VAR([PATSHOME],[the home of the ATS2 compiler])

AC_ARG_VAR([PKGCONFIG_PATSHOME],
  [The PATSHOME setting to put in the pkg-config file [default="${PATSHOME}"]])
if test -z "${PKGCONFIG_PATSHOME}"; then
  PKGCONFIG_PATSHOME="${PATSHOME}"
fi
if test -z "${PKGCONFIG_PATSHOME}"; then
  AC_MSG_ERROR([Please set PKGCONFIG_PATSHOME on the configure command line.])
fi

AM_CONDITIONAL([DEPENDENCY_TRACKING],
  [test x"${enable_dependency_tracking}" != xno])

#--------------------------------------------------------------------------
#
# Checks for programs.

AC_PROG_CC
AC_PROG_CC_C_O
AC_PROG_CXX
AC_PROG_CXX_C_O
AC_CHECK_PROGS([PATSOPT],[patsopt])
AC_PROG_INSTALL
AC_PROG_LN_S
AC_PROG_MAKE_SET
AC_PROG_MKDIR_P
AC_PROG_AWK
AC_PROG_SED
AC_PROG_FGREP
AC_PROG_EGREP

# Enable optional code coverage analysis.
AX_CODE_COVERAGE

PKG_PROG_PKG_CONFIG
PKG_CONFIG="${PKG_CONFIG} --define-variable=PATSHOME=\"${PATSHOME}\""
PKG_INSTALLDIR

#--------------------------------------------------------------------------
#
# Checks for libraries.

#--------------------------------------------------------------------------
#
# Checks for header files.

#--------------------------------------------------------------------------
#
# Checks for typedefs, structures, and compiler characteristics.

#--------------------------------------------------------------------------
#
# Checks for library functions.

#--------------------------------------------------------------------------

CPPFLAGS="${CPPFLAGS}${CPPFLAGS+ }\$(CODE_COVERAGE_CPPFLAGS)"
CFLAGS="${CFLAGS}${CFLAGS+ }\$(CODE_COVERAGE_CFLAGS)"

# You can use ‘@GNU@’ to make GNU Make constructs unbothersome to
# Automake. (By the way, you often can use ‘$(eval ...)’ as well, but
# @GNU@ here may be better.)
AC_SUBST([GNU],[])

StM_REQUIRE_GNU_MAKE_IN_PATH
StM_CONFIG_MAKEFILES

AC_CONFIG_FILES([ats2-timsort.pc])
#AC_CONFIG_FILES([ats2-timsort-c.pc])
AC_CONFIG_FILES([list-ats-dependencies.dats])

AC_CONFIG_COMMANDS([timsort/DATS/typed-timsort-for-c.dats],
  [for t in pointer \
            int unsigned_int \
            signed_char unsigned_char \
            short unsigned_short \
            long unsigned_long \
            long_long unsigned_long_long \
            float double long_double; do
    funcname="${t}_timsort"
    case "${t}" in
      pointer) t_C="const void *" t_ATS="ptr" ;;

      int) t_C="int" t_ATS="int" ;;
      unsigned_int) t_C="unsigned int" t_ATS="uint" ;;

      signed_char) t_C="signed char" t_ATS="schar" ;;
      unsigned_char) t_C="unsigned char" t_ATS="uchar" ;;

      short) t_C="short" t_ATS="sint" ;;
      unsigned_short) t_C="unsigned short" t_ATS="usint" ;;

      long) t_C="long" t_ATS="lint" ;;
      unsigned_long) t_C="unsigned long" t_ATS="ulint" ;;

      long_long) t_C="long long" t_ATS="llint" ;;
      unsigned_long_long) t_C="unsigned long long" t_ATS="ullint" ;;

      float) t_C="float" t_ATS="float" ;;
      double) t_C="double" t_ATS="double" ;;
      long_double) t_C="long double" t_ATS="ldouble" ;;
    esac
    ${SED} -e 's/@FUNCNAME@/'"${funcname}"'/g' \
           -e 's/@CTYPE@/'"${t_C}"'/g' \
           -e 's/@ATSTYPE@/'"${t_ATS}"'/g' \
           "${srcdir}/timsort/DATS/typed-timsort-for-c.dats.in" \
           > "${builddir}/timsort/DATS/${funcname}.dats"
   done],
   [SED="${SED}"
    srcdir="${srcdir-.}"
    builddir="${builddir-.}"])

AC_OUTPUT

#--------------------------------------------------------------------------
# local variables:
# coding: utf-8
# end:

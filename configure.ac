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
AC_CHECK_PROGS([M4],[m4])
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

AC_CHECK_SIZEOF([int])
AC_CHECK_SIZEOF([signed char])
AC_CHECK_SIZEOF([short])
AC_CHECK_SIZEOF([long])
AC_CHECK_SIZEOF([long long])

AC_CHECK_SIZEOF([unsigned int])
AC_CHECK_SIZEOF([unsigned char])
AC_CHECK_SIZEOF([unsigned short])
AC_CHECK_SIZEOF([unsigned long])
AC_CHECK_SIZEOF([unsigned long long])

AC_CHECK_SIZEOF([float])
AC_CHECK_SIZEOF([double])
AC_CHECK_SIZEOF([long double])

AC_CHECK_SIZEOF([ssize_t])
AC_CHECK_SIZEOF([intptr_t])
AC_CHECK_SIZEOF([intmax_t])

AC_CHECK_SIZEOF([size_t])
AC_CHECK_SIZEOF([uintptr_t])
AC_CHECK_SIZEOF([uintmax_t])

AC_CHECK_SIZEOF([int8_t])
AC_CHECK_SIZEOF([int16_t])
AC_CHECK_SIZEOF([int32_t])
AC_CHECK_SIZEOF([int64_t])

AC_CHECK_SIZEOF([uint8_t])
AC_CHECK_SIZEOF([uint16_t])
AC_CHECK_SIZEOF([uint32_t])
AC_CHECK_SIZEOF([uint64_t])

AC_CHECK_TYPE([__int128_t])
if test x"${ac_cv_type___int128_t}" = xyes; then
  AC_CHECK_SIZEOF([__int128_t])
fi

AC_CHECK_TYPE([__uint128_t])
if test x"${ac_cv_type___uint128_t}" = xyes; then
  AC_CHECK_SIZEOF([__uint128_t])
fi

M4FLAGS="${M4FLAGS} -DSIZEOF_INT=${ac_cv_sizeof_int}"
M4FLAGS="${M4FLAGS} -DSIZEOF_SIGNED_CHAR=${ac_cv_sizeof_signed_char}"
M4FLAGS="${M4FLAGS} -DSIZEOF_SHORT=${ac_cv_sizeof_short}"
M4FLAGS="${M4FLAGS} -DSIZEOF_LONG=${ac_cv_sizeof_long}"
M4FLAGS="${M4FLAGS} -DSIZEOF_LONG_LONG=${ac_cv_sizeof_long_long}"

M4FLAGS="${M4FLAGS} -DSIZEOF_UNSIGNED_INT=${ac_cv_sizeof_unsigned_int}"
M4FLAGS="${M4FLAGS} -DSIZEOF_UNSIGNED_CHAR=${ac_cv_sizeof_unsigned_char}"
M4FLAGS="${M4FLAGS} -DSIZEOF_UNSIGNED_SHORT=${ac_cv_sizeof_unsigned_short}"
M4FLAGS="${M4FLAGS} -DSIZEOF_UNSIGNED_LONG=${ac_cv_sizeof_unsigned_long}"
M4FLAGS="${M4FLAGS} -DSIZEOF_UNSIGNED_LONG_LONG=${ac_cv_sizeof_unsigned_long_long}"

M4FLAGS="${M4FLAGS} -DSIZEOF_FLOAT=${ac_cv_sizeof_float}"
M4FLAGS="${M4FLAGS} -DSIZEOF_DOUBLE=${ac_cv_sizeof_double}"
M4FLAGS="${M4FLAGS} -DSIZEOF_LONG_DOUBLE=${ac_cv_sizeof_long_double}"

M4FLAGS="${M4FLAGS} -DSIZEOF_SSIZE_T=${ac_cv_sizeof_ssize_t}"
M4FLAGS="${M4FLAGS} -DSIZEOF_INTPTR_T=${ac_cv_sizeof_intptr_t}"
M4FLAGS="${M4FLAGS} -DSIZEOF_INTMAX_T=${ac_cv_sizeof_intmax_t}"

M4FLAGS="${M4FLAGS} -DSIZEOF_SIZE_T=${ac_cv_sizeof_size_t}"
M4FLAGS="${M4FLAGS} -DSIZEOF_UINTPTR_T=${ac_cv_sizeof_uintptr_t}"
M4FLAGS="${M4FLAGS} -DSIZEOF_UINTMAX_T=${ac_cv_sizeof_uintmax_t}"

M4FLAGS="${M4FLAGS} -DSIZEOF_INT8_T=${ac_cv_sizeof_int8_t}"
M4FLAGS="${M4FLAGS} -DSIZEOF_INT16_T=${ac_cv_sizeof_int16_t}"
M4FLAGS="${M4FLAGS} -DSIZEOF_INT32_T=${ac_cv_sizeof_int32_t}"
M4FLAGS="${M4FLAGS} -DSIZEOF_INT64_T=${ac_cv_sizeof_int64_t}"

M4FLAGS="${M4FLAGS} -DSIZEOF_UINT8_T=${ac_cv_sizeof_uint8_t}"
M4FLAGS="${M4FLAGS} -DSIZEOF_UINT16_T=${ac_cv_sizeof_uint16_t}"
M4FLAGS="${M4FLAGS} -DSIZEOF_UINT32_T=${ac_cv_sizeof_uint32_t}"
M4FLAGS="${M4FLAGS} -DSIZEOF_UINT64_T=${ac_cv_sizeof_uint64_t}"

if test x"${ac_cv_type___int128_t}" = xyes; then
  M4FLAGS="${M4FLAGS} -DSIZEOF_INT128_T=${ac_cv_sizeof___int128_t}"
fi
AM_CONDITIONAL([HAVE_INT128_T],[test x"${ac_cv_type___int128_t}" = xyes])

if test x"${ac_cv_type___uint128_t}" = xyes; then
  M4FLAGS="${M4FLAGS} -DSIZEOF_UINT128_T=${ac_cv_sizeof___uint128_t}"
fi
AM_CONDITIONAL([HAVE_UINT128_T],[test x"${ac_cv_type___uint128_t}" = xyes])

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

AC_SUBST([M4FLAGS])

StM_REQUIRE_GNU_MAKE_IN_PATH
StM_CONFIG_MAKEFILES

AC_CONFIG_FILES([ats2-timsort.pc])
#AC_CONFIG_FILES([ats2-timsort-c.pc])
AC_CONFIG_FILES([list-ats-dependencies.dats])
AC_CONFIG_FILES([common-macros.m4])
AC_CONFIG_FILES([timsort-macros.m4])

AC_OUTPUT

#--------------------------------------------------------------------------
# local variables:
# coding: utf-8
# end:

# -*- autoconf -*-
#
# Copyright (C) 2013 Khaled Hosny and Barry Schwartz
# 
# Copying and distribution of this file, with or without modification,
# are permitted in any medium without royalty provided the copyright
# notice and this notice are preserved.  This file is offered as-is,
# without any warranty.

# serial 2

# -------------------------------------------------------------------------
# These macros call AX_CHECK_GNU_MAKE from the GNU Autoconf Archive
# <http://www.gnu.org/software/autoconf-archive/>
# -------------------------------------------------------------------------

# StM_PROG_GNU_MAKE
# --------------------
#
# A wrapper around AX_CHECK_GNU_MAKE to let the GNU Make command be
# set and used through the precious variable GNU_MAKE.
#
AC_DEFUN([StM_PROG_GNU_MAKE],[{ :;
  AC_ARG_VAR([GNU_MAKE],[GNU Make command])
  test -n "${GNU_MAKE}" && _cv_gnu_make_command="${GNU_MAKE}"
  AX_CHECK_GNU_MAKE
  GNU_MAKE="${_cv_gnu_make_command}"
}])

# StM_REQUIRE_GNU_MAKE
# --------------------
#
# Call AX_CHECK_GNU_MAKE (_not_ StM_PROG_GNU_MAKE), and then tell the
# user to use GNU Make, if it is not installed.
#
# If you use this macro, you might want to have a GNUmakefile and
# either no Makefile or a Makefile that says to use GNU Make.
#
AC_DEFUN([StM_REQUIRE_GNU_MAKE],[{ :;
  AX_CHECK_GNU_MAKE
  if test -z "${_cv_gnu_make_command}"; then
     AC_MSG_ERROR([To build ${PACKAGE}, you should use GNU Make.
           The homepage for GNU make is http://www.gnu.org/software/make/])
  fi
}])

# StM_REQUIRE_GNU_MAKE_IN_PATH
# ----------------------------
#
# Call StM_PROG_GNU_MAKE, and then tell the user to install GNU Make
# in $PATH, if GNU Make is not found.
#
# If you use this macro, you likely also want to use
# StM_CONFIG_MAKEFILES.
#
AC_DEFUN([StM_REQUIRE_GNU_MAKE_IN_PATH],[{ :;
  StM_PROG_GNU_MAKE
  if test -z "${_cv_gnu_make_command}"; then
     AC_MSG_ERROR([To build ${PACKAGE}, the GNU Make command must be in
           your \$PATH or specified by the environment variable `GNU_MAKE'.
           The homepage for GNU Make is http://www.gnu.org/software/make/])
  fi
}])

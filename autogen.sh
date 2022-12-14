#!/bin/sh
# Run this script to generate or regenerate the `configure' script,
# in cases where `autoreconf', etc., alone might not suffice,
# for instance just after cloning one of our Git, Mercurial, or
# Bazaar repositories.

# Sorts Mill Autogen
# <https://bitbucket.org/sortsmill/sortsmill-autogen>
#
# Copyright (C) 2013, 2015 Khaled Hosny and Barry Schwartz
# 
# Copying and distribution of this file, with or without modification,
# are permitted in any medium without royalty provided the copyright
# notice and this notice are preserved.  This file is offered as-is,
# without any warranty.


# Sorts Mill developers: please increase the serial number when you
# make any significant change to this script in its own repository:
#
# serial 3

#
# FIXME: Accept a command line and provide help and version messages
# as usual.
#

progname=`basename "${0}"`

test -n "${srcdir}" || srcdir=`dirname "$0"`
test -n "${srcdir}" || srcdir='.'

newline='
'

not_word='[^_0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz]'

echo_n() {
    # Like `echo -n' but hopefully less system-dependent.
    # (Unfortunately, it will remove _all_ newlines.)
    echo ${1+"$@"} | tr -d "${newline}"
}

grep_word_quietly() {
    pattern="${1}"
    shift
    if LC_ALL=C grep "^${pattern}\$" ${1+"$@"} \
        2> /dev/null > /dev/null; then
        true
    elif LC_ALL=C grep "${not_word}${pattern}\$" ${1+"$@"} \
        2> /dev/null > /dev/null; then
        true
    elif LC_ALL=C grep "^${pattern}${not_word}" ${1+"$@"} \
        2> /dev/null > /dev/null; then
        true
    else
        false
    fi
}

have_autoconf_m4() {
    test -d m4 -a -f "m4/${1}" || test -f "${1}"
}

find_autoconf_m4() {
    if test -d m4 -a -f "m4/${1}"; then
        echo "m4/${1}"
    elif test -f "${1}"; then
        echo "${1}"
    else
        echo "${progname}: possible internal error: find_autoconf_m4 may have been called incorrectly."
        echo "It also is possible the source files were modified while ${progname} was running."
        exit 86
    fi
}

need_sortsmill_tig() {
    # If sortsmill-tig.m4 is included in the package, then we do not
    # need TIG to do the autoreconf.
    test -f configure.ac && \
        grep_word_quietly 'StM_PROG_SORTSMILL_TIG' configure.ac  && \
        ! have_autoconf_m4 sortsmill-tig.m4
}

need_pkg_config() {
    # If pkg.m4 is included in the package, then we do not need
    # pkg-config to do the autoreconf.
    test -f configure.ac && \
        grep_word_quietly \
        'PKG_\(CHECK_MODULES\|PROG_PKG_CONFIG\|CHECK_EXISTS\|INSTALLDIR\|NOARCH_INSTALLDIR\|CHECK_VAR\)' \
        configure.ac && \
        ! have_autoconf_m4 pkg.m4
}

need_gnulib_tool() {
    test -f m4/gnulib-cache.m4 -a ! -f lib/Makefile.am
}

need_gperf_for_gnulib() {
    if have_autoconf_m4 gnulib-comp.m4; then
        grep 'gperf' `find_autoconf_m4 gnulib-comp.m4` \
            2> /dev/null > /dev/null
    else
        false
    fi
}

need_intltoolize() {
    test -f configure.ac && \
        grep_word_quietly 'IT_PROG_INTLTOOL' configure.ac
}

need_autoreconf() {
    test -f configure.ac
}

require_command() {
    echo_n "Checking for ${1}... "
    if which "${1}" 2> /dev/null > /dev/null; then
        which "${1}"
    else
        echo "not found"
        echo ""
        echo "***  ${1} was not found in \$PATH. Please install ${1}."
        if test -n "${2}"; then
            echo "***  See <${2}>"
        fi
        if test -n "${3}"; then
            echo "***  ${3}"
        fi
        exit 1
    fi
}

require_sortsmill_tig() {
    require_command sortsmill-tig \
        'https://bitbucket.org/sortsmill/sortsmill-tig'
}

require_pkg_config() {
    require_command pkg-config \
        'http://www.freedesktop.org/wiki/Software/pkg-config/' \
        "Your operating system may have a \`pkg-config' or \`pkgconfig' package."
}

require_gnulib_tool() {
    require_command gnulib-tool \
        'http://www.gnu.org/software/gnulib/' \
        "Your operating system may have a \`gnulib' package."
}

require_gperf() {
    require_command gperf \
        'http://www.gnu.org/software/gperf/' \
        "Your operating system may have a \`gperf' package."
}

require_intltoolize() {
    require_command intltoolize \
        'http://freedesktop.org/wiki/Software/intltool/' \
        "Your operating system may have an \`intltool' package."
}

require_autoreconf() {
    require_command autoreconf \
        'http://www.gnu.org/software/autoconf/' \
        "Your operating system may have packages for GNU autoconf,
***  automake, libtool, and gettext, some or all of which might
***  be needed."
}

run_gnulib_tool() {
    echo "Running gnulib-tool --update"
    gnulib-tool --update || exit $?
}

run_intltoolize() {
    echo "Running intltoolize --copy --force --automake"
    intltoolize --copy --force --automake || exit $?
}

run_autoreconf() {
    echo "Running autoreconf --force --install --verbose"
    autoreconf --force --install --verbose || exit $?
}

make_function_directives() {
    printf 'BUILT_SOURCES += %s_timsort.dats\n' "$1" >> "$2"
    printf 'CLEANFILES += %s_timsort.dats\n' "$1" >> "$2"
    printf 'CLEANFILES += %s_timsort_dats.c\n' "$1" >> "$2"
    printf 'TIMSORT_ATS_SRC += %s_timsort.dats\n' "$1" >> "$2"
    printf 'TIMSORT_C_SRC += %s_timsort_dats.c\n' "$1" >> "$2"
    printf '%s_timsort.dats: typed-timsort-for-c.dats.m4 common-macros.m4 timsort-macros.m4\n' "$1" >> "$2"
	printf '\t@$(MKDIR_P) $(@D)\n' >> "$2"
    printf '\t$(call v,M4)$(M4) $(TOTAL_M4FLAGS) -DTYPE=%s -DREENTRANT=no $(<) > $(@)\n' "$1" >> "$2"
}

make_function_r_directives() {
    printf 'BUILT_SOURCES += %s_timsort_r.dats\n' "$1" >> "$2"
    printf 'CLEANFILES += %s_timsort_r.dats\n' "$1" >> "$2"
    printf 'CLEANFILES += %s_timsort_r_dats.c\n' "$1" >> "$2"
    printf 'TIMSORT_ATS_SRC += %s_timsort_r.dats\n' "$1" >> "$2"
    printf 'TIMSORT_C_SRC += %s_timsort_r_dats.c\n' "$1" >> "$2"
    printf '%s_timsort_r.dats: typed-timsort-for-c.dats.m4 common-macros.m4 timsort-macros.m4\n' "$1" >> "$2"
	printf '\t@$(MKDIR_P) $(@D)\n' >> "$2"
    printf '\t$(call v,M4)$(M4) $(TOTAL_M4FLAGS) -DTYPE=%s -DREENTRANT=yes $(<) > $(@)\n' "$1" >> "$2"
}

make_test_directives() {
    #
    # Put source files in a subdirectory, to avoid there being
    # multiple rules for tests/.dirstamp
    #
    # See
    # https://stackoverflow.com/questions/11958626/make-file-warning-overriding-commands-for-target
    #
    printf 'TESTS += tests/test-%s_timsort\n' "$1" >> "$2"
    printf 'EXTRA_PROGRAMS += tests/test-%s_timsort\n' "$1" >> "$2"
    printf 'BUILT_SOURCES += tests/src/test-%s_timsort.c\n' "$1" >> "$2"
    printf 'CLEANFILES += tests/test-%s_timsort\n' "$1" >> "$2"
    printf 'CLEANFILES += tests/src/test-%s_timsort.c\n' "$1" >> "$2"
    printf 'nodist_tests_test_%s_timsort_SOURCES =\n' "$1" >> "$2"
    printf 'nodist_tests_test_%s_timsort_SOURCES += tests/src/test-%s_timsort.c\n' "$1" "$1" >> "$2"
    printf 'tests_test_%s_timsort_SOURCES =\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_SOURCES += ats2-timsort.h\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_DEPENDENCIES =\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_DEPENDENCIES += libats2-timsort-c.la\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_CPPFLAGS =\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_CPPFLAGS += $(AM_CPPFLAGS)\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_LDADD =\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_LDADD += libats2-timsort-c.la\n' "$1" >> "$2"
    printf 'tests/src/test-%s_timsort.c: tests/test-timsort-c.c.m4 common-macros.m4 timsort-macros.m4\n' \
           "$1" >> "$2"
	printf '\t@$(MKDIR_P) $(@D)\n' >> "$2"
    printf '\t$(call v,M4)$(M4) $(TOTAL_M4FLAGS) -DTYPE=%s -DREENTRANT=no $(<) > $(@)\n' "$1" >> "$2"
}

make_test_r_directives() {
    #
    # Put source files in a subdirectory, to avoid there being
    # multiple rules for tests/.dirstamp
    #
    # See
    # https://stackoverflow.com/questions/11958626/make-file-warning-overriding-commands-for-target
    #
    printf 'TESTS += tests/test-%s_timsort_r\n' "$1" >> "$2"
    printf 'EXTRA_PROGRAMS += tests/test-%s_timsort_r\n' "$1" >> "$2"
    printf 'BUILT_SOURCES += tests/src/test-%s_timsort_r.c\n' "$1" >> "$2"
    printf 'CLEANFILES += tests/test-%s_timsort_r\n' "$1" >> "$2"
    printf 'CLEANFILES += tests/src/test-%s_timsort_r.c\n' "$1" >> "$2"
    printf 'nodist_tests_test_%s_timsort_r_SOURCES =\n' "$1" >> "$2"
    printf 'nodist_tests_test_%s_timsort_r_SOURCES += tests/src/test-%s_timsort_r.c\n' "$1" "$1" >> "$2"
    printf 'tests_test_%s_timsort_r_SOURCES =\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_r_SOURCES += ats2-timsort.h\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_r_DEPENDENCIES =\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_r_DEPENDENCIES += libats2-timsort-c.la\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_r_CPPFLAGS =\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_r_CPPFLAGS += $(AM_CPPFLAGS)\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_r_LDADD =\n' "$1" >> "$2"
    printf 'tests_test_%s_timsort_r_LDADD += libats2-timsort-c.la\n' "$1" >> "$2"
    printf 'tests/src/test-%s_timsort_r.c: tests/test-timsort-c.c.m4 common-macros.m4 timsort-macros.m4\n' \
           "$1" >> "$2"
	printf '\t@$(MKDIR_P) $(@D)\n' >> "$2"
    printf '\t$(call v,M4)$(M4) $(TOTAL_M4FLAGS) -DTYPE=%s -DREENTRANT=yes $(<) > $(@)\n' "$1" >> "$2"
}

make_ats2_timsort_c_am() {
    f='ats2-timsort-c.am'

    echo "Creating ${f}"

    rm -f "${f}"
    printf '# This file is generated by %s\n' `basename $0` >> "${f}"

    for t in pointer \
             float double long_double \
             int unsigned_int \
             signed_char unsigned_char \
             short unsigned_short \
             long unsigned_long \
             long_long unsigned_long_long \
             ssize_t size_t \
             intptr_t uintptr_t \
             intmax_t uintmax_t \
             int8_t uint8_t \
             int16_t uint16_t \
             int32_t uint32_t \
             int64_t uint64_t; do
        printf '\n' >> "${f}"
        make_function_directives "${t}" "${f}"
        make_function_r_directives "${t}" "${f}"
        make_test_directives "${t}" "${f}"
        make_test_r_directives "${t}" "${f}"
    done

    for t in int128_t uint128_t \
             float32 float64 float128 \
             float32x float64x float128x \
             decimal32 decimal64 decimal128; do
        T=`echo ${t} | tr 'abcdefghijklmnopqrstuvwxyz' 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'`
        printf '\n' >> "${f}"
        printf 'if HAVE_%s\n' "${T}" >> "${f}"
        make_function_directives "${t}" "${f}"
        make_function_r_directives "${t}" "${f}"
        make_test_directives "${t}" "${f}"
        make_test_r_directives "${t}" "${f}"
        printf 'endif HAVE_%s\n' "${T}" >> "${f}"
    done
}

# Run everything in a subshell, so the user does not get stuck in a
# new directory if the process is interrupted.
(
    cd "${srcdir}"

    make_ats2_timsort_c_am

    need_sortsmill_tig && require_sortsmill_tig
    need_pkg_config && require_pkg_config
    need_gnulib_tool && require_gnulib_tool
    need_intltoolize && require_intltoolize
    need_autoreconf && require_autoreconf

    if need_gnulib_tool; then
        run_gnulib_tool
        need_gperf_for_gnulib && require_gperf
    fi
    need_intltoolize && run_intltoolize
    need_autoreconf && run_autoreconf
)

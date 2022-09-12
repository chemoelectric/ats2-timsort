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

.DELETE_ON_ERROR:

ACLOCAL_AMFLAGS = -I m4 --install
AUTOMAKE_OPTIONS =
AUTOMAKE_OPTIONS += foreign
AUTOMAKE_OPTIONS += subdir-objects
AUTOMAKE_OPTIONS += -Wno-portability

include $(top_srcdir)/aminclude_static.am
@GNU@ include $(top_srcdir)/silent-rules.mk
@GNU@ -include ats-dependencies/*.mk

EXTRA_DIST =
MOSTLYCLEANFILES =
CLEANFILES =
DISTCLEANFILES =
BUILT_SOURCES =
AM_M4FLAGS =
AM_CPPFLAGS =
AM_CFLAGS =
AM_LDFLAGS =
LDADD =
bin_PROGRAMS =
lib_LTLIBRARIES =
EXTRA_PROGRAMS =
TESTS =
nobase_nodist_pkginclude_HEADERS =
nodist_pkgconfig_DATA =

EXTRA_DIST += $(srcdir)/silent-rules.mk
EXTRA_DIST += COPYING
EXTRA_DIST += INSTALL
EXTRA_DIST += README
EXTRA_DIST += AUTHORS

DISTCLEANFILES += Makefile
DISTCLEANFILES += GNUmakefile

AM_CPPFLAGS += -I$(builddir)
AM_CPPFLAGS += -I$(srcdir)
AM_CPPFLAGS += -I$(PATSHOME)
AM_CPPFLAGS += -I$(PATSHOME)/ccomp/runtime/

LDADD += $(CODE_COVERAGE_LIBS)

CODE_COVERAGE_IGNORE_PATTERN =
CODE_COVERAGE_IGNORE_PATTERN += /usr/include/*
CODE_COVERAGE_IGNORE_PATTERN += /usr/include/*/*
CODE_COVERAGE_IGNORE_PATTERN += $(PATSHOME)/ccomp/runtime/*
CODE_COVERAGE_IGNORE_PATTERN += $(PATSHOME)/prelude/CATS/*

clean-local: code-coverage-clean tests-clean
distclean-local: code-coverage-dist-clean ats-includes-distclean

#--------------------------------------------------------------------------

TOTAL_M4FLAGS =
TOTAL_M4FLAGS += $(AM_M4FLAGS)
TOTAL_M4FLAGS += $(M4FLAGS)
TOTAL_M4FLAGS += $(XM4FLAGS)

%.dats: %.dats.m4 common-macros.m4 timsort-macros.m4
	@$(MKDIR_P) $(@D)
	$(call v,M4)$(M4) $(TOTAL_M4FLAGS) $(<) > $(@)

#--------------------------------------------------------------------------

PATSOPT_DEPS =

AM_PATSOPTFLAGS =
AM_PATSOPTFLAGS += -IATS $(builddir)
AM_PATSOPTFLAGS += -IATS $(srcdir)

TOTAL_PATSOPTFLAGS =
TOTAL_PATSOPTFLAGS += $(AM_PATSOPTFLAGS)
TOTAL_PATSOPTFLAGS += $(PATSOPTFLAGS)
TOTAL_PATSOPTFLAGS += $(XPATSOPTFLAGS)

TESTS_PATSOPTFLAGS =
TESTS_PATSOPTFLAGS += -IATS $(builddir)/tests
TESTS_PATSOPTFLAGS += -IATS $(srcdir)/tests

@GNU@ define write-dependencies-file =
@GNU@	$(MKDIR_P) ats-dependencies && \
@GNU@		echo $(1): $(shell ./list-ats-dependencies $(2)) \
@GNU@			> ats-dependencies/`echo $(@) | $(SED) 's|/|_057_|g'`.mk
@GNU@ endef

.PHONY: ats-includes-distclean
ats-includes-distclean:
	-rm -f -R ats-dependencies

if DEPENDENCY_TRACKING

%_sats.c: %.sats $(PATSOPT_DEPS) list-ats-dependencies
	@$(call write-dependencies-file,$(@),$(<))
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -s $(<)

%_dats.c: %.dats $(PATSOPT_DEPS) list-ats-dependencies
	@$(call write-dependencies-file,$(@),$(<))
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -d $(<)

%_tests.c: %.dats $(PATSOPT_DEPS) list-ats-dependencies
	@$(call write-dependencies-file,$(@),$(<))
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) \
			$(TESTS_PATSOPTFLAGS) -d $(<)

else !DEPENDENCY_TRACKING

%_sats.c: %.sats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -s $(<)

%_dats.c: %.dats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -d $(<)

%_tests.c: %.dats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) \
			$(TESTS_PATSOPTFLAGS) -d $(<)

endif !DEPENDENCY_TRACKING

%_depsprog.c: %.dats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -d $(<)

#--------------------------------------------------------------------------
#
# The ATS2 library.
#

lib_LTLIBRARIES += libats2-timsort.la

BPTR_SATS = timsort/SATS/bptr.sats
BPTR_DATS = timsort/DATS/bptr.dats
BPTR_SATS_C = timsort/SATS/bptr_sats.c
BPTR_DATS_C = timsort/DATS/bptr_dats.c
CLEANFILES += $(BPTR_SATS_C)
CLEANFILES += $(BPTR_DATS_C)
BPTR_CATS = timsort/CATS/bptr.cats

ARRAY_TIMSORT_SATS = timsort/SATS/array-timsort.sats
ARRAY_TIMSORT_DATS = timsort/DATS/array-timsort.dats
ARRAY_TIMSORT_SATS_C = timsort/SATS/array-timsort_sats.c
ARRAY_TIMSORT_DATS_C = timsort/DATS/array-timsort_dats.c
CLEANFILES += $(ARRAY_TIMSORT_SATS_C)
CLEANFILES += $(ARRAY_TIMSORT_DATS_C)
ARRAY_TIMSORT_HATS = timsort/HATS/array-timsort.hats

TIMSORT_COMMON_SATS = timsort/SATS/COMMON/timsort-common.sats
TIMSORT_COMMON_DATS = timsort/DATS/COMMON/timsort-common.dats
TIMSORT_COMMON_SATS_C = timsort/SATS/COMMON/timsort-common_sats.c
TIMSORT_COMMON_DATS_C = timsort/DATS/COMMON/timsort-common_dats.c
CLEANFILES += $(TIMSORT_COMMON_SATS_C)
CLEANFILES += $(TIMSORT_COMMON_DATS_C)

TIMSORT_CATS = timsort/CATS/timsort.cats

nobase_dist_pkginclude_HEADERS =
nobase_dist_pkginclude_HEADERS += $(BPTR_SATS)
nobase_dist_pkginclude_HEADERS += $(BPTR_DATS)
nobase_dist_pkginclude_HEADERS += $(BPTR_CATS)
nobase_dist_pkginclude_HEADERS += $(ARRAY_TIMSORT_SATS)
nobase_dist_pkginclude_HEADERS += $(ARRAY_TIMSORT_DATS)
nobase_dist_pkginclude_HEADERS += $(TIMSORT_COMMON_SATS)
nobase_dist_pkginclude_HEADERS += $(TIMSORT_COMMON_DATS)
nobase_dist_pkginclude_HEADERS += $(ARRAY_TIMSORT_HATS)
nobase_dist_pkginclude_HEADERS += $(TIMSORT_CATS)

nodist_libats2_timsort_la_SOURCES =
nodist_libats2_timsort_la_SOURCES += $(BPTR_SATS_C)
nodist_libats2_timsort_la_SOURCES += $(BPTR_DATS_C)
nodist_libats2_timsort_la_SOURCES += $(ARRAY_TIMSORT_SATS_C)
nodist_libats2_timsort_la_SOURCES += $(ARRAY_TIMSORT_DATS_C)
nodist_libats2_timsort_la_SOURCES += $(TIMSORT_COMMON_SATS_C)
nodist_libats2_timsort_la_SOURCES += $(TIMSORT_COMMON_DATS_C)
libats2_timsort_la_DEPENDENCIES =
libats2_timsort_la_DEPENDENCIES += $(TIMSORT_CATS)
libats2_timsort_la_DEPENDENCIES += $(BPTR_CATS)

#--------------------------------------------------------------------------
#
# The C library.
#

lib_LTLIBRARIES += libats2-timsort-c.la

TIMSORT_ATS_SRC =
TIMSORT_C_SRC =

$(TIMSORT_ATS_SRC): typed-timsort-for-c.dats.m4

include $(top_srcdir)/ats2-timsort-c.am

nodist_libats2_timsort_c_la_SOURCES =
nodist_libats2_timsort_c_la_SOURCES += $(TIMSORT_C_SRC)
nodist_libats2_timsort_c_la_SOURCES += timsort-for-c-memory_dats.c
dist_libats2_timsort_c_la_SOURCES =
dist_libats2_timsort_c_la_SOURCES += ats2-timsort.h
dist_libats2_timsort_c_la_SOURCES += timsort-for-c-memory.h

nobase_dist_pkginclude_HEADERS += ats2-timsort.h

timsort-for-c-memory_dats.$(OBJEXT): timsort-for-c-memory.include.c

CLEANFILES += timsort-for-c-memory_dats.c

EXTRA_DIST += typed-timsort-for-c.dats.m4
EXTRA_DIST += timsort-for-c-memory.dats
EXTRA_DIST += timsort-for-c-memory.include.c

#--------------------------------------------------------------------------

EXTRA_DIST += tests/test-timsort-c.c.m4

TESTS += tests/test-clz
EXTRA_PROGRAMS += tests/test-clz
CLEANFILES += tests/test-clz
CLEANFILES += tests/test-clz_tests.c
EXTRA_DIST += tests/test-clz.dats
tests_test_clz_SOURCES =
tests_test_clz_SOURCES += tests/test-clz_tests.c
tests_test_clz_DEPENDENCIES =
tests_test_clz_DEPENDENCIES += tests/test-clz.dats
tests_test_clz_DEPENDENCIES += timsort/CATS/timsort.cats
tests_test_clz_CPPFLAGS =
tests_test_clz_CPPFLAGS += $(AM_CPPFLAGS)
tests_test_clz_LDADD =
tests/test-clz_tests.c: tests/test-clz.dats

TESTS += tests/test-minrun
EXTRA_PROGRAMS += tests/test-minrun
CLEANFILES += tests/test-minrun
CLEANFILES += tests/test-minrun_tests.c
EXTRA_DIST += tests/test-minrun.dats
tests_test_minrun_SOURCES =
tests_test_minrun_SOURCES += tests/test-minrun_tests.c
tests_test_minrun_DEPENDENCIES =
tests_test_minrun_DEPENDENCIES += tests/test-minrun.dats
tests_test_minrun_DEPENDENCIES += timsort/CATS/timsort.cats
tests_test_minrun_CPPFLAGS =
tests_test_minrun_CPPFLAGS += $(AM_CPPFLAGS)
tests_test_minrun_LDADD =
tests/test-minrun_tests.c: tests/test-minrun.dats

TESTS += tests/test-nodepower
EXTRA_PROGRAMS += tests/test-nodepower
CLEANFILES += tests/test-nodepower
CLEANFILES += tests/test-nodepower_tests.c
EXTRA_DIST += tests/test-nodepower.dats
tests_test_nodepower_SOURCES =
tests_test_nodepower_SOURCES += tests/test-nodepower_tests.c
tests_test_nodepower_DEPENDENCIES =
tests_test_nodepower_DEPENDENCIES += tests/test-nodepower.dats
tests_test_nodepower_DEPENDENCIES += timsort/CATS/timsort.cats
tests_test_nodepower_CPPFLAGS =
tests_test_nodepower_CPPFLAGS += $(AM_CPPFLAGS)
tests_test_nodepower_CPPFLAGS += -DATS_MEMALLOC_LIBC
tests_test_nodepower_LDADD =
tests/test-nodepower_tests.c: tests/test-nodepower.dats

TESTS += tests/test-galloping
EXTRA_PROGRAMS += tests/test-galloping
CLEANFILES += tests/test-galloping
CLEANFILES += tests/test-galloping_tests.c
EXTRA_DIST += tests/test-galloping.dats
tests_test_galloping_SOURCES =
tests_test_galloping_SOURCES += tests/test-galloping_tests.c
tests_test_galloping_DEPENDENCIES =
tests_test_galloping_DEPENDENCIES += tests/test-galloping.dats
tests_test_galloping_DEPENDENCIES += timsort/CATS/timsort.cats
tests_test_galloping_CPPFLAGS =
tests_test_galloping_CPPFLAGS += $(AM_CPPFLAGS)
tests_test_galloping_CPPFLAGS += -DATS_MEMALLOC_LIBC
tests_test_galloping_LDADD =
tests/test-galloping_tests.c: tests/test-galloping.dats

TESTS += tests/test-merges
EXTRA_PROGRAMS += tests/test-merges
CLEANFILES += tests/test-merges
CLEANFILES += tests/test-merges_tests.c
EXTRA_DIST += tests/test-merges.dats
tests_test_merges_SOURCES =
tests_test_merges_SOURCES += tests/test-merges_tests.c
tests_test_merges_DEPENDENCIES =
tests_test_merges_DEPENDENCIES += tests/test-merges.dats
tests_test_merges_DEPENDENCIES += timsort/CATS/timsort.cats
tests_test_merges_CPPFLAGS =
tests_test_merges_CPPFLAGS += $(AM_CPPFLAGS)
tests_test_merges_CPPFLAGS += -DATS_MEMALLOC_LIBC
tests_test_merges_LDADD =
tests/test-merges_tests.c: tests/test-merges.dats

TESTS += tests/test-array_timsort
EXTRA_PROGRAMS += tests/test-array_timsort
CLEANFILES += tests/test-array_timsort
CLEANFILES += tests/test-array_timsort_tests.c
EXTRA_DIST += tests/test-array_timsort.dats
tests_test_array_timsort_SOURCES =
tests_test_array_timsort_SOURCES += tests/test-array_timsort_tests.c
tests_test_array_timsort_DEPENDENCIES =
tests_test_array_timsort_DEPENDENCIES += tests/test-array_timsort.dats
tests_test_array_timsort_DEPENDENCIES += timsort/CATS/timsort.cats
tests_test_array_timsort_DEPENDENCIES += libats2-timsort.la
tests_test_array_timsort_CPPFLAGS =
tests_test_array_timsort_CPPFLAGS += $(AM_CPPFLAGS)
tests_test_array_timsort_CPPFLAGS += -DATS_MEMALLOC_LIBC
tests_test_array_timsort_LDADD =
tests_test_array_timsort_LDADD += libats2-timsort.la
tests/test-array_timsort_tests.c: tests/test-array_timsort.dats

TESTS += tests/test-timing-array_timsort
EXTRA_PROGRAMS += tests/test-timing-array_timsort
CLEANFILES += tests/test-timing-array_timsort
CLEANFILES += tests/test-timing-array_timsort_tests.c
EXTRA_DIST += tests/test-timing-array_timsort.dats
tests_test_timing_array_timsort_SOURCES =
tests_test_timing_array_timsort_SOURCES += tests/test-timing-array_timsort_tests.c
tests_test_timing_array_timsort_SOURCES += tests/Perry-Nadkarni/timsort.c
tests_test_timing_array_timsort_SOURCES += tests/Perry-Nadkarni/timsort.h
tests_test_timing_array_timsort_SOURCES += tests/Perry-Nadkarni/timsort-impl.h
tests_test_timing_array_timsort_DEPENDENCIES =
tests_test_timing_array_timsort_DEPENDENCIES += tests/test-timing-array_timsort.dats
tests_test_timing_array_timsort_DEPENDENCIES += timsort/CATS/timsort.cats
tests_test_timing_array_timsort_DEPENDENCIES += libats2-timsort.la
tests_test_timing_array_timsort_CPPFLAGS =
tests_test_timing_array_timsort_CPPFLAGS += $(AM_CPPFLAGS)
tests_test_timing_array_timsort_CPPFLAGS += -DATS_MEMALLOC_LIBC
tests_test_timing_array_timsort_LDADD =
tests_test_timing_array_timsort_LDADD += libats2-timsort.la
tests/test-timing-array_timsort_tests.c: tests/test-timing-array_timsort.dats

tests-clean:
	-rm -f tests/*.$(OBJEXT)

#--------------------------------------------------------------------------
#
# Computation of dependencies.
#

EXTRA_PROGRAMS += list-ats-dependencies
EXTRA_DIST += list-ats-dependencies.dats
CLEANFILES += list-ats-dependencies
CLEANFILES += list-ats-dependencies_depsprog.c

nodist_list_ats_dependencies_SOURCES =
nodist_list_ats_dependencies_SOURCES += list-ats-dependencies_depsprog.c
list_ats_dependencies_CPPFLAGS =
list_ats_dependencies_CPPFLAGS += $(AM_CPPFLAGS)
list_ats_dependencies_CPPFLAGS += -DATS_MEMALLOC_LIBC
list_ats_dependencies_DEPENDENCIES =
list_ats_dependencies_DEPENDENCIES += list-ats-dependencies.dats
list_ats_dependencies_LDADD =
list_ats_dependencies_LDADD += -L'$(PATSHOME)/ccomp/atslib/lib'
list_ats_dependencies_LDADD += -latslib

#--------------------------------------------------------------------------

nodist_pkgconfig_DATA += ats2-timsort.pc
#nodist_pkgconfig_DATA += ats2-timsort-c.pc

#--------------------------------------------------------------------------
# local variables:
# coding: utf-8
# end:

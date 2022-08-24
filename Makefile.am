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
AM_CPPFLAGS =
AM_CFLAGS =
AM_LDFLAGS =
LDADD =
bin_PROGRAMS =
lib_LTLIBRARIES =
EXTRA_PROGRAMS =
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
# ARRAY_TIMSORT_HATS = timsort/HATS/array-timsort.hats

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
# nobase_dist_pkginclude_HEADERS += $(ARRAY_TIMSORT_HATS)
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

# TESTS =

# EXTRA_DIST += tests/test-arrays-stability.dats
# EXTRA_DIST += tests/test-arrays-patterns-stable.common.dats
# EXTRA_DIST += tests/test-arrays-patterns-unstable.common.dats

# TESTS += tests/test-arrays-stability
# EXTRA_PROGRAMS += tests/test-arrays-stability
# CLEANFILES += tests/test-arrays-stability
# CLEANFILES += tests/test-arrays-stability_tests.c
# tests_test_arrays_stability_SOURCES =
# tests_test_arrays_stability_SOURCES += tests/test-arrays-stability_tests.c
# tests_test_arrays_stability_DEPENDENCIES =
# tests_test_arrays_stability_DEPENDENCIES += tests/test-arrays-stability.dats
# tests_test_arrays_stability_DEPENDENCIES += libats2-timsort.la
# tests_test_arrays_stability_DEPENDENCIES += $(TIMSORT_HATS)
# tests_test_arrays_stability_CPPFLAGS =
# tests_test_arrays_stability_CPPFLAGS += $(AM_CPPFLAGS)
# tests_test_arrays_stability_CPPFLAGS += -DATS_MEMALLOC_LIBC
# tests_test_arrays_stability_LDADD =
# tests_test_arrays_stability_LDADD += libats2-timsort.la
# tests/test-arrays-stability_tests.c: tests/test-arrays-stability.dats

# include $(top_srcdir)/test-arrays-patterns-stable.am
# include $(top_srcdir)/test-arrays-patterns-unstable.am

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

# nodist_pkgconfig_DATA += ats2-timsort.pc

#--------------------------------------------------------------------------
# local variables:
# coding: utf-8
# end:

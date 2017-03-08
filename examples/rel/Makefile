#FLAGS=
#LIB=

OTHERFLAGS+=$(FLAGS) $(LIB)
FSTAR_HOME=../..
include ../Makefile.include

uall: all

all: ifc\
		 random_tapes\
		 delimited_release\
		 recursive

ifc:
	$(FSTAR) rel.fst whilelanguage.fst ifc.fst ifcExample.fst

random_tapes:
	$(FSTAR) bijection.fst random_tapes.fst

recursive:
	$(FSTAR) recursive.fst

delimited_release:
	$(FSTAR) delimited_release.fst

WhileReify:
	$(FSTAR) --include ../../dm4free WhileReify.fst


CFSTAR=$(subst CURRENT_DIR,examples/rel,$(CVERFSTAR))
all-cver:
	$(CFSTAR) rel.fst whilelanguage.fst ifc.fst ifcExample.fst
	$(CFSTAR) bijection.fst random_tapes.fst
	$(CFSTAR) recursive.fst
	$(CFSTAR) delimited_release.fst

# makefile for Pawns stuff - try out make pattern rules etc

# Size of tree for testing bst.pns, pbst.pns (if Max=0 we use a default
# small list and test some higher order stuff). If Max>1400 or so its
# too big without GC for some default limits on process size etc.
# not actually used - see code
Max=12000
Max=30000
Max=0

# gcc -O3 does a great job
# for Max=30000 without -O pbst gets killed but is ~3.5 times bst
# without -O we get bst 12.5s, pbst 30+?s, cbst  2.4s,  gcbst 2.3s
#   with -O3 we get bst  0.81, pbst 16.67s, cbst 1.65s, gcbst 1.64s
# A bit weird...?
CC=gcc

# adt stuff causes *lots* of warnings due to implicit coercion between
# things with size sizeof(void*) currently, so we turn off all warnings
# with -w (for now XXX useful to have them when mixing C and Pawns)
CFLAGS=-w
CFLAGS=-O3 -w

# We need to link with the (Boehm++) garbage collector currently, which
# should really be installed somewhere standard, but just in case its
# not. gc details at http://www.hboehm.info/gc/
GCLIB=~/lib/gc/lib
GC=gc
LDLIBS=-Wl,-rpath -Wl,$(GCLIBDIR) -l$(GC)
# LDFLAGS=-Wl,-rpath -Wl,$(GCLIBDIR) -l$(GC)


# install these somewhere, eg ~/bin at least
PNSC=~/bin/pnsc
ADTPP=../../../adt4c/src/adtpp
ADTPP=~/bin/adtpp

# The Pawns "compiler" converts foo.pns to foo.c and foo.adt and the
# latter is converted to foo.h by adtpp.  foo.c requires foo.h and
# foo.adt should generally not be touched by the user so we can package
# up these two steps together as follows.  Make doesn't clean up foo.h
# or foo.adt, but we might want to use the former in our C code and the
# latter can easily be cleaned up and is small anyway.
# adtpp is currently rather noisey so we put the output in a file
# (XXX we include pawns.h as a dependency here for development purposes)
%.c %.h : %.pns pawns.h
	$(PNSC) $<
	$(ADTPP) $*.adt > adtpp.errs

# the adtpp tool takes a foo.adt file and generates a foo.h file
# (not needed for Pawns if we use the combined rule but it does no harm
# and can be useful for C code)
%.h : %.adt
	$(ADTPP) $<

.bogus: all
all: bst pbst cbst cpinfbst cpibst cpbst cpigbst hssbst hspbst hsrbst mlpbst mlrbst

.bogus: times
times: all
	echo
	echo '------------ Pawns with DU'
	-time ./bst
	echo
	echo '------------ C with malloc, DU'
	-time ./cbst
# 	echo
# 	echo '------------ C with GC_malloc'
# 	-time ./gcbst
	echo
	echo '------------ MLton with Ref, DU'
	-time ./mlrbst
	echo
	echo '------------ Haskell with STRef, DU'
	-time ./hsrbst
	echo
	echo '------------ MLton no DU'
	-time ./mlpbst
	echo
	echo '------------ Pawns no DU'
	-time ./pbst
	echo
	echo '------------ C iterative GC_malloc no free no DU'
	-time ./cpinfbst
	echo
	echo '------------ Haskell with seq but no DU'
	-time ./hssbst
	echo
	echo '------------ C iterative GC_malloc no DU'
	-time ./cpigbst
	echo
	echo '------------ C iterative no DU'
	-time ./cpibst
	echo
	echo '------------ C no DU'
	-time ./cpbst
	echo
	echo '------------ Haskell no DU'
	-time ./hspbst

# bst.pns imports bstmain.pns
bst.c : bst.pns bstmain.pns

# pbst.pns imports bstmain.pns
pbst.c : pbst.pns bstmain.pns

gcbst.c : cbst.c
	tail -n +3 cbst.c > gcbst.c

cpigbst.c : cpibst.c
	tail -n +3 cpibst.c > cpigbst.c

# should do cpinfbst.c like above

cbst.o : cbst.c bst.h

cpbst.o : cpbst.c bst.h

cpinfbst.o : cpinfbst.c bst.h

cpibst.o : cpibst.c bst.h

cpigbst.o : cpigbst.c bst.h

gcbst.o : gcbst.c bst.h

hspbst : hspbst.hs
	ghc -O3 $<

hssbst : hssbst.hs
	ghc -O3 $<

hsrbst : hsrbst.hs
	ghc -O3 $<

mlpbst : mlpbst.sml
	mlton $<

mlrbst : mlrbst.sml
	mlton $<

.bogus: clean
clean:
	rm -f *.adt *.o *.h.gch bst.h bst.c pbst.h pbst.c adtpp.errs
	rm -f hsrbst.hi hssbst.hi hspbst.hi tmp* a.out
	-rm -i bst pbst cpinfbst cpibst cpbst cbst cpigbst gcbst hsrbst hssbst hspbst mlpbst mlrbst

# makefile for Pawns stuff - try out make pattern rules etc

# Size of tree for testing bst.pns, pbst.pns (if Max=0 we use a default
# small list and test some higher order stuff). If Max>1400 or so its
# too big without GC for some default limits on process size etc.
Max=12000
Max=30000
Max=0

# gcc -O3 does a great job
CC=gcc

# We need to link with the (Boehm++) garbage collector currently, which
# should really be installed somewhere standard, but just in case its
# not. gc details at http://www.hboehm.info/gc/
GCLIB=~/lib/gc/lib
GC=gc
LDLIBS=-Wl,-rpath -Wl,$(GCLIBDIR) -l$(GC)
# LDFLAGS=-Wl,-rpath -Wl,$(GCLIBDIR) -l$(GC)

# adt stuff causes *lots* of warnings due to implicit coercion between
# things with size sizeof(void*) currently, so we turn off all warnings
# with -w (for now XXX useful to have them when mixing C and Pawns)
CFLAGS=-O3 -w
CFLAGS=-O3 -w -DREDIRECT_MALLOC=GC_malloc -DIGNORE_FREE
CFLAGS=-O3 -w


# XXX install these somewhere, eg ~/bin at least
PNSC=../compiler/pnsc
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

# An alternative is to separate these and change the generic %.o : %.c
# rule so it requires a %.h as well, as follows:
# %.o : %.c %.h
# 	$(CC) $(CPPFLAGS) -c $< -o $@
# 
# %.c %.adt : %.pns
# 	$(PAWNSC) $<

# the adtpp tool takes a foo.adt file and generates a foo.h file
# (not needed for Pawns if we use the combined rule but it does no harm
# and can be useful for C code)
%.h : %.adt
	$(ADTPP) $<

allbst: bst pbst bst_poly

pawns.h: ../compiler/pawns.h
	cp $< .

builtin.h: ../compiler/builtin.h
	cp $< .

apply.h: ../compiler/apply.h
	cp $< .

# bst.pns imports from addlist.pns, io.pns so we put the following dependency
bst.c: bst.pns addlist.pns io.pns pawns.h builtin.h

bst_poly.c: bst_poly.pns addlist.pns io.pns pawns.h builtin.h

bst_count.c: bst_count.pns io.pns random.pns pawns.h builtin.h

pbst.c: pbst.pns addlist.pns io.pns pawns.h builtin.h

p1bst.c: p1bst.pns addlist.pns io.pns pawns.h builtin.h

# bst, pbst use main() defined in bst_main.c (not bst_main.pns)
bst: bst.o bst_main.o io.o addlist.o

bst_poly: bst_poly.o bst_main.o io.o addlist.o

bst_count: bst_count.o bst_main.o io.o random.o addlist.o

pbst: pbst.o bst_main.o io.o addlist.o

p1bst: p1bst.o bst_main.o io.o addlist.o

bst_main.o: bst.h bst_main.c addlist.h
	gcc -c $(CFLAGS) -DMax=$(Max) bst_main.c

# testio.pns imports from io.pns so we put the following dependency
testio.c: testio.pns io.pns pawns.h builtin.h

isort.c: isort.pns array.pns io.pns pawns.h builtin.h

isort: isort_main.c isort.c io.c

testuf.c: testuf.pns union_find.pns io.pns pawns.h builtin.h

.bogus: test
test: bst pbst p1bst isort testio
	echo TESTING bst:::::::::::::::::::::::::::::::::::: > /dev/null
	./bst
	echo TESTING pbst:::::::::::::::::::::::::::::::::::: > /dev/null
	./pbst
	echo TESTING p1bst:::::::::::::::::::::::::::::::::::: > /dev/null
	./p1bst
	echo TESTING isort:::::::::::::::::::::::::::::::::::: > /dev/null
	./isort
	echo TESTING testio:::::::::::::::::::::::::::::::::::: > /dev/null
	./testio < testio.pns
	echo DONE :::::::::::::::::::::::::::::::::::: > /dev/null

.bogus: clean
clean:
	rm -f *.adt *.o *.h.gch bst.h bst.c bst_poly.c p1bst.h pbst.h p1bst.c \
		pbst.c testio.c wam.c wam.h bst_count.c bst_count.h \
		io.c io.h imp.c imp.h addlist.c addlist.h io.h bst.h bst_poly.h \
		bst1.h wam.h testio.h isort.h isort.c testuf testuf.c testuf.h \
		bst1.c cord_poly.c bst_a.c cord.c ho.c state.c state.h \
		absshare.c eval.c evalp.c queue_du.c queue_du.h tuple.c tuple.h \
		union_find.c union_find.h random.c random.h \
		array.c array.h adtpp.errs
	rm -if testio bst p1bst pbst isort bst_poly bst_count
	rm -if tmp* a.out errs

# :set noet ts=8


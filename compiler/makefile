# makefile for pawns compiler:
# just two SWI-Prolog files with compile/0 as top level pred
# to call

pnsc: pawns.pl comp.pl
	swipl -o pnsc -g compile -c pawns.pl comp.pl

install: pnsc
	cp pnsc ~/bin/pnsc

uninstall:
	rm ~/bin/pnsc

clean:
	rm -rf pnsc tmp*

# :set noet ts=8


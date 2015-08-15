# makefile for pawns compiler:
# just two SWI-Prolog files with compile/0 as top level pred to call
#
# Generate VERSION line with: date +'VERSION = 1.%y%m%d'
# or in vim: :/^VERSION /!date +'VERSION = 1.\%y\%m\%d'
VERSION = 1.150815

pnsc: pawns.pl comp.pl
	swipl -o pnsc -g compile -c pawns.pl comp.pl

install: pnsc
	cp pnsc ~/bin/pnsc

uninstall:
	rm ~/bin/pnsc

Readme.. : Readme.src makefile
	sed s/VERSION/$(VERSION)/ < Readme.src > Readme..
	echo "You might want to: cp Readme.. ../Readme"

clean:
	rm -rf pnsc tmp* Readme..

# :set noet ts=8


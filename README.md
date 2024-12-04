# Pawns, version 1.241204

Pawns (Pointer Assignment Without Nasty Surprises) is a
declarative/imperative language. It supports typical features of a strict
functional language such as algebraic data types, polymorphism, higher
order programming and pure (referentially transparent) functions. It also
supports imperative features such as destructive update via pointers and
a form of global variables (including IO).  Unlike other declarative/imperative
languages, all data constructor arguments can have pointers to them and
be updated, all side-effects in the code are made obvious by annotations
and impure code can be encapsulated inside a pure function. The
compiler checks annotations and purity by analysis of data structure
sharing. Functions that may update their arguments have additional
declarations concerning update and sharing.

Language and implementation by
[Lee Naish](https://lee-naish.github.io/).
It's basicaly a proof of concept for what I think are some neat language
ideas that tackle a difficult problem in programming language design - 
definitely not a polished product!

# Pawns home page
Since 2022 the home page has been https://lee-naish.github.io/src/pawns/
(tinyurl.com/pawns-lang points to an outdated version).
This has links to (among other things):

- A brief overview of the language:  
This is not necessarily up to date, misses some features,
and the syntax is not what is supported - see note below.

- An informal introduction to the language:  
Older than the overview and much harder to read but covers a few more
things.

- Slides for a couple of talks

- A paper on the sharing analysis done in the compiler:  
The implementation
here has some known bugs corrected in the paper, meaning you can write
dodgey code and the compiler won't complain as it should.  See comments
in the source code. However, it also has some enhancements to make sharing
more precise, meaning you can write correct code that passes the compiler
even though the analysis in the paper would result in error messages.
The paper may be updated to reflect this at some point.


# Requirements

The system is also not packaged well currently. My development machine
is laptop running Ubuntu. I've not ported it elsewhere but after doing
several years worth of upgrades it still built with no problems so the
Ubuntu build seems to be on solid foundations.  If you can't get it to
work on your chosen platform I'll gladly return your money but I can't
return your time:(
It needs

- 1) SWI-Prolog:
See https://www.swi-prolog.org/build/unix.html, eg  
sudo apt-get install software-properties-common  
sudo apt-add-repository ppa:swi-prolog/stable  
sudo apt-get update  
sudo apt-get install swi-prolog

- 2) Boehm et al. garbage collector:  
sudo apt-get install libgc-dev

- 3) adtpp tool installed in ~/bin/adtpp:
This is in a public git
repository and requires flex, yacc and gcc.  
sudo apt-get install git  
git clone https://github.com/lee-naish/adtpp  
sudo apt install flex  
sudo apt install bison  
mkdir ~/bin  
cd adtpp/src  
make install

- 4) pawns.h in current directory

- 5) gcc (other C compilers should be ok also)


# Repository contents

- compiler/:
Source for compiler, pnsc.
"pnsc foo.pns" will compile foo.pns to foo.c and foo.adt (algebraic data
type definitions that adtpp will convert to C). See examples/makefile
for make convenient rules etc
To install the compiler in ~/bin, use:
"cd compiler
make install"

- examples/:
Example Pawns code (with makefile and other files needed etc)

- bench:  
Some benchmarks (binary tree insertion...) in various languages


# Syntax

People have always argued way too much about the syntax of programming
languages, at the expense of semantics, which is the important thing.
What was that Phil Wadler quote...?  There are two things I have done
which may counter this trend for Pawns.  First, the papers written so far
have used a fake syntax based on Haskell.  Second, I think we can *all*
agree that the actual supported syntax is awful.  It was chosen to make
the implementation easy - I had better things to do than write a parser
(which would also require more serious thoughts about syntax) so I just
used Prolog syntax with a bunch of operators declared and used 'read'
in Prolog to do all the parsing.  This means various things need to be
terminated with '.', the Prolog tokeniser is used, and various things
need parentheses or braces.  I have not properly described the syntax -
best look at examples for now.  However, none of this is set in stone.
The start of a Pawns source code file, up to the first blank line,
is ignored as far as code is concerned.  It can be used for a #! line,
meta-data, directives etc.  These could include a directive to say what
syntax is used in the rest of the file.  Currently its just ignored,
so best make sure you start with a block of comments or at least a blank
line, or your first bit of code will mysteriously get ignored.


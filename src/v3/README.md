# ET version 2, UFO strikes back

## Intro

This tarball contains sources for the ET (formerly IPL) interpreter.
ET is a ML-like language with the strong normalization property.  It's
mainly meant for research.

This is the third implementation of ET.


## Compilation

In order to compile ET you need OCaml distribution. I tried with 3.06
and later versions.  You need ocamlc, ocamllex and ocamlyacc, that all
come with the OCaml distribution.  No library beside standard OCaml
libraries is needed.

In addition to OCaml you need GNU Make.  A binary executable of GNU Make
for MS Windows is included with this source distribution.

This version of ET was tested on the PLD Linux, FreeBSD and Windows XP
operating systems.

To compile ET just type `make` (or `gmake` if you're on BSD).


## Installation

None yet.  Just run et from current directory.  It needs to find
`startup.et` file.


## Authors

The language was invented by Zdzisław Spławski <splawski@ci.pwr.wroc.pl>.
This implementation of interpreter was written by Michał Moskal <michal@moskal.me>.


## Reference Manual

Please consult the `doc/iplman1.pdf` file for a description of the previous
implementation of ET, by ToMasz Wierzbicki. This implementation provides very
similar interface, changes are described below.

This section can be thought of as a kind of mental patch.


### Changes

All special type constructors, beside ->, are simply defined in the
startup.et file. They are often referred to as in IPL, with special
symbols, though they real names can sometimes show up.

The `del` declaration is not supported.

`quit;` in the `use`-ed file, kill the interpreter.

Comments can be nested, though contents of the comment is not lexed, so
"" have no special meaning within it.

The interpreter does not care about symbol redefinition, so be careful
not to override something from the `startup.et` file, other wise Bad Things
Will Happen To You [tm].


### New features

There are a few new syntactic conventions.

"\x. y" stands for "fn x => y". The \-form is also used in the output.

"let" can be used instead of "val", the OCaml like "let x = y in z"
is not supported, use "let val x = y; in z end".

"quit;" is an alias to the "exit;". 

A new declaration "set" has been introduced. "set" is followed by an
identifier or a string. Both mean the same thing. Following "set"
arguments are supported:

* debug, nodebug -- control some debugging output during mon/amon invocations, in short -- don't use.
* quiet, noquiet -- whether to output types of the values defined, and definitions of introduced type iterators, recursors etc.

The reasonable use of the "set" declaration is as follows:

    set quiet;
    (* some program *)
    set noquiet;
    (* some interesting part of the program *)
    set quiet;
    (* blah *)
    set noquiet;

in a file of course.

Apart from syntax -- user input from each session is stored in the
"session.et" file in the current directory.  It is overwritten each time.

Wrocław, 2003, 2004.

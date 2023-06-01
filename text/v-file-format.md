- Title: v file format (grammar)

- Driver: Enrico

- Status: (Early) Draft

----

# Summary

Defining a structure/grammar for Coq documents.  Today .v files inherit the "script to replay" nature of the original "UI" of Coq, a REPL.
As a consequence any command can occur almost everywhere.

## Problems
* it is not the case any command works in any context.  We do have bugs today.

## Benefits
* simplify the code of commands (no need to check where the command is run and/or take special measures).  E.g. Require in the middle of make-your-pick
* give more structure to the document to ease the life of tools
* improve on checking speed (parallel checking is simpler with structure at hand)

## Caveat
* as close as possible to "clean" Coq documents already there, no big syntactic change.
* grammar ready for 8.6, so that one can check it, even if Coq takes little or no advantage of it

## Ideas
* additional parsing rules placed in the header (and processed upfront) of a file or sub-block (section, module) to be able to parse the entire document without executing it.  Is that possible with modules?
* occasion to add syntax for *explicit* dependencies: this depends on that (for classes of objects: this hind db, these ltac definitions, these section vars).  A mix of statically visible dependencies and user provided ones, hopefully suggested by Coq after an execution.
* Axioms put upfront, at least their names.

## Mockup

```
V format 1 compat 8.5 (* eventual compat mode *)

(* Header. *)

From … Require … .

Set Options. (* not for retro compat *)

Reserve Notation "…" .

(* Body. *)

..

Section A. (* Block *)

Reserve Notation "…".

...

End. (* End Block *)

```

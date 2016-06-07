- Title: Import Name Modifiers

- Drivers: Jason

- Implementors: Pierre-Marie(?)

- Status: Draft

----

# Summary

This document descibes a proposal to satisfy
[feature request #4615](https://coq.inria.fr/bugs/show_bug.cgi?id=4615),
allowing users to rename or hide identifiers on import.  This is
based on
[Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.Modules#mods)
and [Haskell](https://wiki.haskell.org/Import).

# Syntax

The following are typical examples:
```coq
Import Coq.Program.Basics (using (impl, apply), renaming (compose to comp), using Notation ("g ∘ f")).
From Coq.Program.Basics Import using (impl, apply), renaming (compose to comp), using Notation ("g ∘ f").
From Coq.Program.Basics Import hiding (impl), using Notation ("g ∘ f").
From Coq.Program.Basics Import renaming (impl to implication), renaming Notation ("g ∘ f" to "g \o f").
```

## Grammar

Here is a possible grammar for the minimal feature set (note that we use the template definition `ne_<foo>_list ::= <foo> | <foo>, ne_<foo>_list`):
```
import_or_export                ::= "Import"|"Export"
import_or_export_directive      ::= import_or_export module_with_attributes ... module_with_attributes "."
from_import_or_export_directive ::= "From" module_path import_or_export ne_attribute_list "."
module_with_attributes          ::= module_path | module_path" "(" ne_attribute_list ")"
attribute                       ::= "using" "(" [ne_ident_list] ")"
                                  | "hiding" "(" [ne_ident_list] ")"
                                  | "renaming" "(" ne_renaming_list ")"
                                  | "as" ident
renaming                        ::= ident "to" ident
```
Note that `notation_string`s are to be enclosed in double quotes.

If we want to support notations, instances, hints, modules, etc, we might use:
```
import_or_export                ::= "Import"|"Export"
import_or_export_directive      ::= import_or_export module_with_attributes ... module_with_attributes "."
from_import_or_export_directive ::= "From" module_path import_or_export ne_attribute_list "."
module_with_attributes          ::= module_path | module_path" "(" ne_attribute_list ")"
attribute                       ::= "using" [ident_modifier] ["(" [ne_ident_list] ")"]
                                  | "using" notation_modifier ["(" [ne_notation_string_list] ")"]
                                  | "using" "Hints" ["(" ne_hintdb_list ")"]
                                  | "hiding" [ident_modifier] ["(" [ne_ident_list] ")"]
                                  | "hiding" notation_modifier ["(" [ne_notation_string_list] ")"]
				  | "hiding" "Hints" ["(" [ne_hintdb_list] ")"]
                                  | "renaming" ["Ltac"] "(" ne_renaming_list ")"
                                  | "renaming" notation_modifier "(" ne_renaming_notation_list ")"
renaming                        ::= ident "to" ident
renaming_notation               ::= notation_string "to" notation_string
ident_modifier                  ::= "Ltac" | "Instance" | "Arguments"
notation_modifier               ::= "Notation" | "Infix"
```

# Semantics

For any modifier, (`ident_modifier`, `notation_modifier`, no
modifier), having both a `using` directive and a `hiding` directive is
an error, but any other combination is permissible.

The default is to import nothing; the following are equivalent:
```coq
Import M ().
Import M (hiding).
Import M (using ()).
From M Import hiding.
From M Import using ().
```
Importantly, notations are not imported, and if hints and settings
eventually follow `Import` rather than `Require`, then they should not
be imported here.

Note that `hiding` and `using ()` are equivalent, and `hiding ()` and
`using` are equivalent.  Everything mentioned in any `using` list, or
in the complement of any hiding list, shall be imported (made
available with an unqualified name).

The directive `renaming (x to y)` on a module `M` shall be roughly equivalent to:
```coq
Local Notation y := M.x.
```
More precisely, it should add the names `y`, `M.y`, `path.to.M.y`,
etc., to the table of names, all pointing to the kernel name of `M.x`.

The directive `renaming Ltac (x to y)` on a module `M` shall be equivalent to
```coq
Local Ltac y := M.x.
```
More precisely, it should add the names `y`, `M.y`, `path.to.M.y`,
etc., to the table of Ltac names, all pointing to the kernel name of
`M.x`.

The directive `renaming Notation ("foo" to "bar")` shall be as if
every instance of `Notation "foo" := stuff` (modulo differences in
spacing that do not matter to the parser) were copied to be `Local
Notation "bar" := stuff` in the current file (using fully qualified
names).  `Infix` shall be similar.

The directive `renaming Notation ("foo"%foo_scope to "bar"%bar_scope)`
shall be as if every instance of `Notation "foo" := stuff : foo_scope`
(modulo differences in spacing that do not matter to the parser) were
copied to be `Local Notation "bar" := stuff : bar_scope` in the
current file (using fully qualified names).  `Infix` shall be similar.

Importantly, the original notations are still accessible if an `Import
M` is later issued.

If hints are made to follow `Import` rather than `Require`, then
`using Hint (dbs)` will add the hints in `M` in the databases `dbs` to
the dbs in this module.

## Changes
* 2016-07-06, first draft

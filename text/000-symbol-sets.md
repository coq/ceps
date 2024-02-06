- Title: Symbol Sets

- Drivers: Michael Soegtrop

----

# Summary

In automation the most reliable and fastest way to reduce terms is frequently to use the `lazy` reduction with an explicit list of symbols to expand, that is:
```
lazy [ <some symbols> ].
```

The problem with this is that the symbol sets can be lengthy - a few 100 is not rare in practice - and difficult to maintain.
Typically the symbol sets are all symbols from specific modules with individual inclusions / exclusions.
An effective solution would be to be able to declare named symbol sets using
- individual symbols
- all symbols in a module without recursion into sub modules
- all symbols in a module with recursion into sub modules
- set operations union, intersection and difference

# Motivation

In proof automation one frequently has to reduce terms which contain user supplied terms, that is terms whose content the automation does not restrict.
Applying `simpl` or `cbn` to such terms does not work reliably, because there are examples for term where `simpl` and `cbn` take a very long time.
If the user supplied terms are of this nature, the overall tactic will also take a long time, even though the task at hand in the automation would be trivial.
Besides in automation one usually does not want the user supplied terms to be changed at all.

What is done in some Coq developments is to hide the user supplied terms behind opaque definitions and then use full evaluation.
This works, but the hiding and unhiding of user terms can take substantially longer than the reduction itself.

The only really good option is using `lazy` or `cbv` with a delta symbol set, which just contains private definitions of the automated tactic itself.
This  requires an effective way to manage symbol sets.

Note that this method frequently involves copying some basic functions like list append.
This is usually not a problem - it can become a problem if the automation needs e.g. arithmetic.
It would make sense to have a mechanism to copy the contents of a module under a new logical path, so that one can add the copy to the delta reduction list, but leave the original symbols unreduced.
But this is an independent topic and should be discussed in a separate CEP.

Note that this related to [Declare Reduction](https://coq.inria.fr/doc/V8.19.0/refman/proofs/writing-proofs/equality.html#coq:cmd.Declare-Reduction).

# Detailed design

The syntax doesn't really matter a lot - it is fine to choose something which is easy to implement.

A possible syntax would be:
- Command **Declare Symbol Set** *ident* **:=** *symbol_set_expr*
- *symbol_set_expr* ::= **Module** *qualid* | **Module Recursive** *qualid* | *reference* | *symbol_set_expr* [**+ * -**] *symbol_set_expr* | **(** *symbol_set_expr* **)**

where
- **Module** *qualid* adds all symbols directly found in the module or library specified by *qualid*
- **Module Recursive** *qualid* adds all symbols found in the module or library specified by *qualid* and all its sub modules
- *reference* adds the one symbol *reference*
- *A* **+** *B* adds the union of *A* and *B*
- *A* **-** *B* adds the *A* excluding *B* (set difference)
- *A* * *B* adds the intersection of *A* and *B*

The Coq grammar token [reductions](https://coq.inria.fr/doc/V8.19.0/refman/proofs/writing-proofs/equality.html#grammar-token-reductions) should be extended with a new item `set <symbol-set-id>`.

It is required to be able to extend the symbol set in the tactic call either by allowing an additional `delta` (not not `delta -`), of by providing APIs in the common tactic languages to create new symbol sets from existing ones.
It would also make sense to provide APIs to define symbol sets from tactics.

# Drawbacks

None I am aware of.

# Alternatives

One can create symbol sets using Elpi programs and there is work in progress to add functionality to enumerate modules to Ltac2 as well.
This does work, but the concept is so basic, that direct support in Coq does make sense.
I guess the idea behind [Declare Reduction](https://coq.inria.fr/doc/V8.19.0/refman/proofs/writing-proofs/equality.html#coq:cmd.Declare-Reduction) is similar, but a comfortable way to handle symbol sets is required.
Good support for creating symbol sets will likely encourage more people to use this very effective technique.
It is also imaginable that for very large list there might be more effective ways to process the reduction tactic if the symbol set is stored internally in an appropriate format.
If symbol sets are provided as lists, the reduction tactic has to at least traverse this list once.

There are ways to control the opacity of symbols, including local control using `with_strategy`, but this proved to be more useful for manual proofs than for proof automation.

# Unresolved questions

The precise syntax of the symbol set declaration command.

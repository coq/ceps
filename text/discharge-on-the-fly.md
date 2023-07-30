- Title: Discharge on the fly

- Drivers: Hugo Herbelin

----

# Summary

After the refactoring of discharge made in coq/coq#14727, it becomes possible to discharge declarations at the time of their declaration. We discuss a proposal in this direction.

# Motivation

It is common in a section to want to temporarily generalize the notions defined in the section but to continue to work in the context of the section for further developments, as in:

```coq
Section S.
Context {A B:Type}.
Inductive option := None | Some (a:A).
Definition map (f : A -> B) (o : option) :=
  match o with
  | None => Top.None
  | Some a => Top.Some (f a)
  end.
(* ... *)
End S.
```

This is what the proposal tends to achieve.

# Details about the design

## Basic idea

The basic proposal is to emulate a section
```coq
Section S.
Variable a : A.
Definition f := ...
```
as
```coq
Definition f a := ...
Module S.
Parameter a : A.
Definition f := ...
```

that is, that each persistent declaration of the section is declared both in the section and, discharged, at toplevel (as well as appropriately discharged in all intermediary section levels).

The resulting full names are typically `Top.f` for the toplevel copy, and `Top.S.f` for the copy in the section (as well as `Top.S.T.f`, etc., if there are nested sections).

At the end of the section, the module being built is discarded.

The distributivity of declarations over section levels is obtained by maintaining one environment/state for each section level:
- opening a section forks a new copy of the current environment/state for the section; this copy becomes the active one
- extending a section content enriches simultaneously and hereditarily all section levels (i.e. `Definition f := t` adds `Top.f` to all section levels, `Top.S.f` to all section levels from level `Top.S`, `Top.S.T.f` to all section levels from level `Top.S.T`, etc.); there are however three kinds of declarations (see below)
- closing a section drops the active copy of the environment/state and makes active the environment/state of the outer section (which itself growed since the fork)

## Definitionally connecting the different copies

Different strategies are possible to definitionally relate the different copies.

- The body of the constant is in the fully discharged copy and each copy in a section takes the form:
  ```
  Definition f := Top.f a.
  ```

  How to evaluate the risk that the encoding surfaces too easily (e.g. when reducing), losing the advantages of reasoning in a section?

- Each copy has a full copy of the body discharged accordingly to the level of section where it lives without the less generalized copy evaluating to the more generalized one. This provides convertibility of `Top.f a` and `Top.S.f` for transparent constants but not for opaque constants or inductive types. For opaque constants and inductive types, a possibility would be that the conversion algorithm takes into account a table of correspondences between `Top.f a` and `Top.S.f`.

## Which authoritative definition?

The pre-existing model gets the typability of the fully-discharged declarations by trusting the type-checking of the non-discharged declarations and trusting the discharge algorithm.

From the moment all copies are generated at the same time, it would reduce the trusted type-checking basis of documents whose sections are closed to instead type the fully-discharged declaration (see @gares' [suggestion](https://github.com/coq/coq/pull/17888#issuecomment-1653536034)). The trust in the discharge algorithm would then serve only to trust the (volative) inner of the sections (via the claim that discharging correctly reverts specialization).

## Three kinds of objects in sections

In practice, relatively to sections, Coq objects are of three kinds:
- volatile: meaningful only in the section it is declared: this is the case of `Variable`, `Hypothesis`, polymorphic universes,  etc.
- generalizable: meaningful in all section levels: this is the case of `Definition`, `Inductive`, `Axiom`, etc.
- global: meaningful in the section-free level: this is the case of `Require`, monomorphic universes, etc.

## Non-logical objects

Implicit arguments, arguments scopes, arguments renamings, ... are attached to a constant and should a priori be present at each level.

For tables, such as coercions, canonical projections, hints, instances, it is unclear what status to give to them.

For instance, having only the generalized form of the coercions would lead to too general coercions whose arguments cannot be inferred. Keeping the less general copy is a priori the safest path for compatibility. Do we need more?

# Compatibility issues

The model adds new names. So, it can in theory introduces new name ambiguities and force to qualify more.

The question of efficiency is also to study. In the minimalistic approach, it is only about moving discharging tasks currently done at the end of a section towards the place where the object is discharged. But keeping several copies of coercions, hints, etc. at all levels may possibly result in slowdowns for e.g. `auto` or type classes resolution.

# The experiment of PR coq/coq#17888

At the time of writing, PR coq/coq#17888 does the following:
- introduces a distinction between the three kinds of objects
- build dynamically the contents of all section levels and inherit their contents from outer sections to inner sections, for both the logical environment and the non-logical state
- "certify" the innermost declaration, but certifying instead the outermost would be easy
- the different discharged copies of a declaration are distinct copies of the original copy (no explicit sharing, no convertibility between opaque constants and inductive types from different section levels)

# Further questions

The model would a priori supports declaring module variables in a section and discharging modules in sections into functors.

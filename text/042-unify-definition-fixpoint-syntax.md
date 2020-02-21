- Title: Unifying the syntax of Theorem, Definition and Fixpoint

- Drivers: Théo Zimmermann

----

# Summary

This CEP proposes to unify the syntax of commands of the `Theorem`
family, of the `Definition` family and the `Fixpoint` and `CoFixpoint`
commands.  All the currently supported syntax forms would be kept.
The different families of commands would become variants whose
semantics differ only on specific and clearly documented points which
could alternatively be set using attributes.  For instance, `Theorem`
would become a strict equivalent of `#[ opaque ] Definition` and
`Fixpoint` a strict equivalent of `#[ recursive ] Definition`.

# Motivation

There are several motivations to this change:

- Supporting `Theorem @ident {? @type } := @term`:

  - Currently there is no way to define an opaque constant by
    providing only its body.

  - In the upcoming refactoring of the reference manual, we would like
    the first chapter to be about the core language that the kernel
    understands.  We couldn't give examples using `Theorem` because
    this command always open the proof mode.  Yet, it is important to
    be able to explain that the kernel can define opaque
    constants, i.e. constants with a body which behave like axioms.

  - It would allow deprecating the akward `Proof @term` syntax.

- Fixing the inconsistent semantics of `Theorem` and `Theorem
  ... with`.  The first syntax form behaves like `Definition` but the
  second one behaves like `Fixpoint`.

  A previous attempted solution was simply to deprecate the `Theorem
  ... with` syntax in favor of `Fixpoint ... with` in proof mode
  ([coq/coq#8265](https://github.com/coq/coq/pull/8265)).  However,
  this syntax is used in CompCert and Xavier Leroy argued in favor of
  keeping it, in particular on the basis that people who read and
  review formalizations might appreciate the distinction of intent
  between a `Theorem` and a `Fixpoint`.  Still, there is no reason why
  we should explicitly distinguish between a `Definition` and a
  `Fixpoint` but not between a non-recursive and a recursive
  `Theorem`.

  The proposed solution is to keep the existing syntax `Theorem
  ... with` but encourage that it comes with an explicit `recursive`
  annotation (in the form of an attribute).  This also opens the way
  to supporting (non-mutually) recursive `#[ recursive ] Theorem`, and
  `#[ recursive ] Definition` as an equivalent to `Fixpoint` to define
  (possibly mutually) recursive objects.

# Detailed design

The current syntax is:

- for `Definition` / `Example`:
  ```
  {| Definition | Example } @ident_decl @def_body

  def_body ::= {* @binder } {? : @type } := {? @reduce } @term
             | {* @binder } : @type
  ```

- for `Fixpoint`:
  ```
  Fixpoint @fix_def {* with @fix_def }

  fix_def ::= @ident_decl {* @binder } {? @fixannot } {? : @type } {? := @term } {? @decl_notations }
  ```

- for `CoFixpoint`:
  ```
  CoFixpoint @cofix_def {* with @cofix_def }

  cofix_def ::= @ident_decl {* @binder } {? : @type } {? := @term } {? @decl_notations }
  ```

- for `Theorem` and variants:
  ```
  @thm_token @ident_decl {* @binder } : @type {* with @ident_decl {* @binder } : @type }

  thm_token ::= Theorem
              | Lemma
              | Fact
              | Remark
              | Corollary
              | Proposition
              | Property
  ```

The new syntax would be:

```
@decl_token @decl_def {* with @decl_def }

decl_token := Definition
            | Example
            | Fixpoint
            | CoFixpoint
            | Theorem
            | Lemma
            | Fact
            | Remark
            | Corollary
            | Proposition
            | Property

decl_def := @ident_decl {* @binder } {? @fixannot } @decl_body {? @decl_notations }

decl_body := {? : @type } := {? @reduce } @term
           | : @type
```

with the following newly supported attributes:

- `recursive` and `corecursive` to declare a fixpoint / cofixpoint:

  - attribute `recursive` is implicit for `Fixpoint` and rejected by
    `CoFixpoint`;
  - attribute `corecursive` is implicit for `CoFixpoint` and rejected
    by `Fixpoint`;
  - attribute `recursive` or `corecursive` is compulsory to use the
    `with` variant of `Definition`;
  - using the `with` variant of `Theorem` without attribute
    `recursive` or `corecursive` raises a deprecation message and is
    interpreted as if `recursive` had been used;
  - the `@fixannot` clause requires the `recursive` attribute
    being used (or implicit in the case of `Fixpoint`).

- `opaque` and `transparent` to declare an object opaque or
  transparent like `Qed` and `Defined` do (note that this is not the
  same as what the `Opaque` and `Transparent` commands do):

  - `transparent` is assumed by default for `Definition`, `Fixpoint`,
    `CoFixpoint` but `opaque` is accepted;
  - `opaque` is assumed by default for `Theorem` and variants but
    `transparent` is accepted.
  - these attributes are only accepted when a body is provided (when
    no body is provided the transparency is determined by the ending
    `Defined` or `Qed`).

# Drawbacks

This creates more ways of doing the same thing.  People could decide
to write things like:

```coq
#[ transparent ]
Theorem not (b : bool) :=
  match b with true => false | false => true end.

#[ opaque ]
Definition not_not_idem (b : bool) : not (not b) = b :=
  match b with true => eq_refl | false => eq_refl end.
```

But it seems consistent with the current philosophy of the language to
give many synonyms for doing the same thing and trusting the user to
produce readable scripts in the end.

# Alternatives

We could keep the syntax separate and keep waiting for users asking
for this or that extension to implement it, but it is unlikely that
the syntax would ever converge, and it would remain inconsistent and
confusing.  The first chapter of the refactored reference manual could
rely on the unsatisfactory `Proof @term` syntax to avoid bringing the
tactics in.

We could decide to go with this plan but not provide the `transparent`
and `opaque` attributes.  This means that when a body is provided,
`Theorem` and `Definition` would not be interchangeable (but they
already mostly are when in proof mode because the `Qed` and `Defined`
commands are not forced upon the user).

We could also decide to implement this plan but make `Definition` and
`Theorem` fully interchangeable.  A `Theorem` with a body would be
transparent by default, an `opaque` attribute could be used on
`Definition` or `Theorem` to make the body opaque.

# Unresolved questions

The name of attributes `opaque` and `transparent` may be confusing
with the `Opaque` and `Transparent` commands which are not as strong.
Maybe another name should be used.  For instance `qed` and `defined`
(this choice would be reminiscent of the proof-mode-ending commands
`Qed` and `Defined`).

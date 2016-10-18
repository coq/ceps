- Title: Econstrs

- Drivers: Pierre-Marie Pédrot

- Status: Draft

----

# Summary

This CEP proposes to give a proper treatment of terms with evars in the ML
implementation, by introducing a new module `Econstr` in the `engine` folder.
Its API would essentially give a way to abstract away from the fact that
terms may contain solved evars.

# Current situation

As of today, higher layers of Coq use the same representation for terms as the
kernel itself, i.e. `Constr.t`. This datastructure is already hidden under
smart constructors and a generic accessor providing an inductive view of a term.

The AST features two tactic-specific nodes, namely `Evar` and `Meta`. Most parts
of the kernel do not handle these nodes and fail when they encounter it, except
notably for reduction. While `Meta` is deprecated and bound to disappear, `Evar`
is the currently preferred way to use partially defined terms.

An *evar* is a unique identifier that only makes sense in a given proof state,
called an *evarmap*, which amongst other things maps evars to their typing
environment and optional body. Terms featuring evars have an evar normal form
(ENF) given a particular environment, built by replacing each defined evar by
its body in the term.

In theory, apart for very specific cases, evar-wearing terms should be
considered equivalent when they have the safe ENF. We call functions that
respect the equivalence insensitive. The problem is that most of the functions
from the codebase are not insensitive, because they rely on `Constr` generic
accessor to observe the shape of a term.

This has two very annoying consequences:

- To enforce insensitivity, most functions normalize the term upfront, which
is in general a costly operation even though the algorithm is only going to
inspect a small part of the term. Evar normalization is indeed a recurring
cost in code from the wild, amounting up to 30% of the total time of tactic
evaluation.

- Worse, even when trying to computing the ENF eagerly, some parts of the code
fail to be insensitive, leading to very subtle heisenbugs really hard to track
down.

# Proposed solution

## Overview

We advocate for the use of a new type statically ensuring insensitivity,
distinct from the `Constr.t` term and defined outside of the kernel.

Such a type would live in a module `Econstr` from the `engine` folder, where
the name refers to standard nomenclature for evar-aware tactics. Internally,
this would be the same type as `Constr.t`, but it would be made opaque
externally and provided with an accessor that would expand evars on the fly.
An API sketch is provided below.

```ocaml
type t
(** This is [Constr.t] internally *)

val of_constr : Constr.t -> t
(** Identity *)

(** Destructor *)

val kind : Evd.evar_map -> t -> (t, t) Constr.kind_of_term
(** Essentially the [Evarutil.kind_of_term_upto] function *)

val to_constr : Evd.evar_map -> t -> Constr.t
(** Essentially the [Evarutil.nf_evar] function *)

(** Constructors *)

(* ... *)

(** Unsafe primitives *)

module Unsafe :
sig

val to_constr : t -> Constr.t
(** Identity *)

end
```

## Pros

- No more need to normalize upfront, as this is done on-the-fly.
- Statical guarantee that functions are insensitive.
- Clear-cut separation between kernel terms and tactic-level terms.

## Cons

- Requires a lot of boilerplate in the transition phase.
- Requires to duplicate code to handle both plain terms and evar terms
- Requires to duplicate datastructures embedding terms

## Potential solutions to the above issues

### Code duplication

The code duplication can be handled through an object-oriented API, thanks
to a view argument.

```ocaml
type ('a, 'b) view = {
  view : 'a -> 'b -> ('b, 'b) Constr.kind_of_term;
  make : ('b, 'b) Constr.kind_of_term -> 'b;
}
```

The `'a` argument stands for the state needed to deconstruct a term, and the
`'b` argument gives the actual term type. An argument of this type would allow to
abstract away from the actual implementation of terms. Two typical
implementations of `view` would be:

```
val constr_view : (unit, Constr.t) view
val econstr_view : (Evd.evar_map, Econstr.t) view
```

All functions taking terms as arguments should be abstracted in a uniform way.
E.g. the function:

```
val foo : constr -> Id.t -> const list
```

should be turned into:

```
val foo : ('a, 'b) view -> 'a -> 'b -> Id.t -> 'b list
```

This may incur a small overhead, though I believe it would be ridiculous
compared to the gain of not computing the ENF upfront. Furthermore, when Coq
gets to use a version of OCaml with implicit modules, this could be turned into
a much more palatable, and probably more efficient, code.

### Type duplication

This issue is more tricky. For opaque types, it is easy to provide the accessors
translating freely terms into evar-terms on the fly without having to duplicate
the corresponding type. For transparent types mentionning terms, this is more
complicated.

Most notably, contexts are defined as lists of algebraic types. I believe that
in this case, the kernel structures should be parameterized by the type of
terms, and the current kernel variants should be defined as instances of such
generic types.

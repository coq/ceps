- Title: Ltac 2.0

- Proposer: Pierre-Marie

----

# Summary

The Ltac tactic language is probably one of the ingredients of the success of
Coq, yet it is at the same time its Achilles' heel. Indeed, Ltac:

- has nothing like intended semantics
- is very non-uniform due to organic growth
- lacks expressivity and requires programming-by-hacking
- is slow
- is error-prone and fragile
- has an intricate implementation

This has a lot of terrible consequences, most notably the fact that it is never
clear whether some observed behaviour is a bug or a proper one.

Following the need of users that start developing huge projects relying 
critically on Ltac, we believe that we should offer a proper modern language
that features at least the following:

- at least informal, predictible semantics
- a typing system
- standard programming facilities (i.e. datatypes)

This CEP aims at the description of this language before implementation,
thereafter called Ltac2.

# General design

There are various alternatives to Ltac, such that Mtac or Rtac for instance.
While those alternatives can be quite distinct from Ltac, we want to design
Ltac2 to be closest as reasonably possible to Ltac, while fixing the
aforementioned defects.

In particular, Ltac2 is going to be:
- a ML language, i.e.
  * a call-by-value functional language
  * with effects
  * together with Hindley-Milner type system
- a language featuring meta-programming facilities for the manipulation of
  Coq-side terms
- a language featuring notation facilities to help writing palatable scripts

We describe more in details each point in the remainder of this document.

# ML component

The call-by-value functional language fragment is easy to implement.

## Syntax

We simply elaborate on the old Ltac syntax, which is quite close to e.g. the one
of OCaml.

```
σ, τ := κ ∈ K | α | σ → τ | ...

t, u := x | n ∈ ℕ | "string" | (fun x => t) | t u | let x := t in u | ...
```

## Reduction

We use the usual ML call-by-value reduction.

Note that this is already a departure from standard Ltac which uses heuristic to
decide when evaluating an expression, e.g.

```
foo (idtac; let x := 0 in bar)

foo (let x := 0 in bar)
```

We would now require an explicit thunk not to compute the argument, and `foo`
would have e.g. type `(unit -> unit) -> unit`.

```
foo (fun () -> let x := 0 in bar)
```

## Typing

Typing is strict and follows Hindley-Milner system. We would not implement the
current hackish subtyping semantics, and one would have to resort to conversion
functions. See notations though to make things more palatable. For instance,
it would be common to use the following.

```
val mkVar : string -> constr
val destVar : constr -> string
```

## Effects

As for the effects, nothing involved here, except that instead of using the
standard IO monad as the ambient effectful world, Ltac2 is going to use the
tactic monad. Monadic glue is implicit, just as in any instance of Moggi's
metalanguage.

The tactic monad is essentially a IO monad, together with backtracking state.
See `engine/proofview.mli` for the primitive operations. It means we have
at the level of Ltac2 some primitives as:

```

============
Γ ⊢ fail : A


Γ ⊢ t : A    Γ ⊢ u : A
======================
    Γ ⊢ t + u : A

 Γ ⊢ t : A    Γ ⊢ u : A
=========================
Γ ⊢ try t with E => u : A

```

The backtracking is first-class, i.e. one can write `0 + 1 : int` producing
a backtracking integer.

We need to solve the focus-on-goal issue though. The tactic monad naturally
operates over the whole proofview, which may represent several goals. It is
natural to do the same here, but we must provide a way to focus and a goal
and express that something is interpreted in a goal. Maybe the following
primitives?

```
val enter : (handle -> 'a) -> 'a list
val hyp : handle -> string -> constr
val goal : handle -> constr
```

An alternative would be to do this implicitly and fail whenever there is not
exactly one goal under focus.

```
val enter : (unit -> 'a) -> 'a list
val hyp : string -> constr (** fail if not focussed *)
val goal : unit -> constr (** fail if not focussed *)
```

In what context do we evaluate a term expression?

# Meta-programming

One of the horrendous implementation problems of Ltac is the fact that it is
never clear whether an object refers to the object world or the meta-world.
This is a source of incredible slowness, as the interpretation must be
aware of bound variables and must use heuristics to decide whether a variable
is a proper one or referring to something in the Ltac context?

Likewise, in current Ltac, constr parsing is implicit, so that `foo 0` is
not `foo` applied to the Ltac integer expression `0` (Ltac does have a
non-first-class notion of integers), but rather the Coq term `Datatypes.O`.

We should stop doing that! We need to mark when quoting and unquoting, although
we need to do that in a short and elegant way so as not to be too cumbersome
to the user. Suggestions include:

```
let var := "H" in (* a string *)
let c := << fun $var$ => 0 >> (* the Coq term "fun H => 0" *)
let c' := << let x := $c$ in nat >> (* the Coq term "let x := fun H => 0 in nat" *)
...

```

We need to decide how to handle bound variables though.

What about the various kind of constrs? Untyped vs. typed, plus caring about
the context?

# Notations

Notations are the crux of the usability of Ltac. We should be able to recover
a feeling similar to the old implementation by using and abusing notations.
This would be done at at level totally different from the semantics, which
is not what is happening as of today.

We would like to attach some scopes to identifiers, so that it could be possible
to write e.g.

```
Ltac intro : string -> unit := ...

Goal True -> True.
Proof.
intro "H". (** We require the quote here, as this is not a notation *)
Undo.
Top.intro "H". (** An alternative way, by fully qualifying the tactic *)
Abort.

Tactic Notation "intro" ident(i) := intro i.

Goal True -> True.
Proof.
intro H.
(** This sequence of tokens is elaborated at parsing time into [Top.intro "H"]
    thanks to the above notation. *)
Undo.
Top.intro "H".
(** Here, the core tactic is still reachable using the fully qualified name *)
Abort.
```

A typical notation that would be useful is the Coq term one, so that the
following is possible.

```
Ltac destruct : constr -> unit := ...

Tactic Notation "destruct" constr(x) := destruct x.

Goal False -> True.
Proof.
intro H. (** assuming we have the previous notation in scope *)
destruct H. (** H is interpreted in the current goal? *)
Undo.
Top.destruct << H >> (** alternative without notation *)
```

Another one, probably useful for transition, would be a scope `legacy_constr`
that parses an identifier s.t. `legacy_constr(H)` elaborates to
`hyp H + mkVar H`.

One should be able to define new scopes, by giving them a qualified name,
a old scope used for the parsing rule, and an expansion macro. We can maybe
unify such a scope creation process with the tactic notation one?

# Transition path

TODO


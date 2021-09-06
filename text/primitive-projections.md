- Title: What model for primitive projections?

----

# Summary

Projections of record fields currently follow different overlapping paths:
- constructors-based vs destructors-based normal forms
- `t.(f params)` vs `f params t` concrete representation
- unfolded `Proj` vs folded `Proj` vs `App` internal representation

This document is an attempt to propose solutions to clarify the picture.

See also [#14640](https://github.com/coq/coq/pull/14640) which tries to set up a context to stabilize a design choice.

## Issue 1: the relative status of `Const`-based projections and `Proj`-based projections

It is common to write `f param t` to mean a compact `Proj` kernel node. It is also useful to have a non compact representation for partial application of a projection or for an unapplied projection. What to do with it?

*Design choice 1*: not a kernel problem: the user (or vernac level) can declare `Definition f' params x := x.(f params)` and use it later as an ordinary definition
  - Advantages: a simple model
  - Drawbacks: the name `f'` is different

*Design choice 2*: Whenever a record is defined, a `Const f` node of same name `f` is made available at the same time and `Proj (f,x)` and `App (Const f, params, x)` are considered convertible by default without needing any form of explicit unfolding. Note that the infrastructure to make them convertible basically already exists in coercions, unification, ...
  - Advantages: the two representations are fully equivalent (up to the compact representation and the loss of the exact form of parameters)
  - Drawbacks: the code to identify `Const` and `Proj` might be considered intrusive (but at least, it is alreay there, using `Projection.constant` and `expand_projection` machinery)

*Design subchoice 2.1*: When the syntax `f params t` is used, does it bind automatically to the compact representation (as it is done now), and thus reprinted as `t.(f params)`?
  - Advantages: compatibility with the current usages
  - Drawbacks: it does some transformation under the carpet

*Design subchoice 2.2*: Any application of `Const f` to enough arguments is automatically turned by `mkApp` into a `Proj` (this assumes that any constant `f` contains an information on its projection status)? In particular, `Const` is used only for non-applied or not-enough-applied projection.
  - Advantages: a simple model; no need to identify `Proj (f,x)` and `App (Const f, params, x)` in conversion
  - Drawbacks: maybe a few incompatibilities due to the dropping of arguments?

Related: [#14084](https://github.com/coq/coq/pull/14084) (`match goal` involving primitive projections) and [#11366](https://github.com/coq/coq/issues/11366) (which requires to be able to declare partially applied projections as coercions).

## Issue 2: the relative status of "folded" vs "unfolded" `Proj` node

*Design choice 1*: The "folded" vs "unfolded" boolean is dropped. Unfolding a `Proj` node is a no-op. In scenario 2.1 of issue 1, unfolding a `Const` denoting a projection reveals a `Proj` node. In scenario 2.2, it is a no-op.

*Design choice 2*: Idem but unfolding a primitive projection applied to the constructor of the record performs the iota-reduction (like in the positive case) instead of a being a no-op.

Related: [#5250](https://github.com/coq/coq/issues/5250), [#5698](https://github.com/coq/coq/issues/5698), [#5699](https://github.com/coq/coq/issues/5699) (effect of unfolding tactics).

See associated [Zulip discussion](https://coq.zulipchat.com/#narrow/stream/237656-Coq-devs.20.26.20plugin.20devs/topic/Primitive.20Projection.20mode).

## Issue 3: the status of `match` and destructing `let` in "primitive" record types
 
See impact of desugaring `match` in terms of complexity ([#13913](https://github.com/coq/coq/pull/13913)) or unification ([#6726](https://github.com/coq/coq/issues/6726), [#9763](https://github.com/coq/coq/issues/9763)) or readability ([#6723](https://github.com/coq/coq/issues/6723)).

*Design choice 1*: keep `match` nodes as they are in primitive record types; they will behave correctly for reduction (that is like their expansion into projections); to deal with them in the conversion, it is enough to extend the conversion with eta-expansions of `match` into projections.

   - Advantages: a priori no break of compatibility for the developments already using `match` on primitive record types

*Design choice 2*: forbid `match` at all on primitive record types (as well as `fun 'pat => ...` and `let 'pat := ... in ...` and `let (x1,...,xn) := ... in ...`), even as a primitive form of sugar, making primitive and non-primitive record types two incompatible styles of formalization.

   - Advantages: model consistent with viewing primitive record types as negative types in polarized logic
   - Drawbacks: unclear how to address the compatibility with existing code

## Issue 4: The status of the `t.(f args)` notation as an alternative notation for any kind of application.

See e.g. [#11332](https://github.com/coq/coq/pull/11332).

*Design choice 1*: Accept the notation `t.(f args)` as a shorthand for `f args t` even when `f` is not a projection even if this is lost at printing time.
  - Advantages: nothing more to do
  - Drawbacks: no printing

*Design choice 2*: Give the ability to declare a table of "methods" supporting the `t.(f args)` notation. Only such registered method can use the notation. The notation is used for printing too. Internally, it is an `App` node.

*Orthogonal design choice*: same as design choices 1 and 2 but with a different notation, e.g `t.{f args}`.

## Issue 5: The representation of projections in "positive" types. Can they take benefit of a compact representation?

*Design choice 1*: We don't make a difference between positive and negative types. Both supports a `Case` and a `Proj` node which behave anyway the same wrt reduction even when we think at them as syntactic sugar. We add eta-rule for `Case` in the conversion, which are the current rules for expansion into `Proj`. The only difference is that `Proj` is mentally thought as in normal form for a negative type and as a short-hand for a `match` for a positive type. As for `Case`, it can either be mentally thought as a short-hand for its let-proj-expansion for a negative type or explicitly expanded in `cbn` and `lazy`, while `Case` for a positive type is in normal form.
   - Advantages: a simple model for the user
   - Drawbacks: not a conventional view in polarized logic

Note: consistency between positive and negative record types would require to add support for named projections of local definitions of records.

*Design choice 2*: Idem but `Proj` expands to `match` in positive types.
   - Advantages: conventional view in polarized logic
   - Drawbacks: `match`-based representation of projections are uselessly verbose

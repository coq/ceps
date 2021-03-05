- Title: Extended subsingleton elimination and subsingleton impredicativity, the case of `SProp`, `Prop` and `hProp`

- Driver: Hugo Herbelin

- Status: Draft

-----

# Bibliography

  - [Definitional Proof-Irrelevance without K](https://hal.inria.fr/hal-01859964v2/document), Gaëtan Gilbert, Jesper Cockx, Matthieu Sozeau, Nicolas Tabareau
  - This [Coq-club thread](https://sympa.inria.fr/sympa/arc/coq-club/2021-02/msg00092.html) on HoTT support

# Summary

The declaration of an inductive type in `SProp` and `Prop` can be seen as a truncation with respect to classes of formulas which we shall respectively call `SProp` and `Prop`.

These truncations are automatically considered as eliminable when the truncated type is syntactically recognized as belonging to the class ("singleton elimination", or "subsingleton elimination").

The classes `Prop` and `SProp` are impredicative, in the sense that a dependent product of codomain `Prop` or `SProp` is again in the class.

This CEP is about three distinct extensions:
- extending the definition of `Prop` and `SProp` classes with new syntactically decidable criteria, avoiding the current need for "proxy" types
- extending the dynamic detection of subsingleton elimination also avoiding the need for "proxy" types
- adding a new class `HProp` providing an impredicative universe of subsingleton types; this extra `HProp` class would provide a variant of HoTT with impredicative `hProp` (`hProp := { A:Type & forall x y:A, x = y }`), alternative to using an axiom of resizing

# Details of the current situation for `Prop` and `SProp`

## `Prop`

### `Prop`-truncation
We call `Prop`-truncation the following type
```
Variant Squash (A:Type) : Prop := squash : A -> Squash A.
```
whose content can be `match`-eliminated only in a context of type `Prop`.

Then, any inductive or coinductive type declared in `Prop` is intended to be equivalent to the `Squash` of its declaration in `Type`.

If the encapsulated type is itself a `Prop`, it can be eliminated. This is called subsingleton elimination because there is a primitive syntactic class of subsingleton types having this property by default:
  - `False`
  - `True`
  - any type previously declared in `Prop` (e.g. `ex A P`, or a smashed type)
  - any type previously declared in `SProp`
  - any sigma-type of such types, as in `and`, possibly recursive as in `Acc`, possibly with indices as in `eq`, possibly also with primitive projections.

If the encapsulated type is not a syntactic `Prop` but only equivalent to a syntactic `Prop`, it can nevertheless be eliminated too by using an indirection. The user has first to eliminate to the proxy type, then go out of `Prop` from the proxy. Avoiding a proxy is the purpose of point 5 below.

Note that the syntactic conditions for being eliminable syntactically define what `Prop` stands for: the smallest subset defined by these conditions. It is not hard-wired that `Prop` is limited to this class and the class could then be extended further. For instance, there is an interpretation of `Prop` as impredicative `Set`, and an other interpretation as impredicative `hProp` (see below).

### Late detection of `Prop`

Sort-polymorphism makes that inductive types are syntactically recognized in `Prop` after instantiation of parameters. For instance, `prod True True` is recognized as impredicative after instantiation:
```
Check Type -> prod True True.
(* Type -> True * True
     : Prop *)
```
Similarly in contexts where a `Prop` is expected:
```
Check and (prod True True) True
(* True * True /\ True
     : Prop *)
```
Contrastingly, subsingleton elimination is not recomputed dynamically:
```
Inductive PROD A B : Prop := PAIR : A -> B -> PROD A B.
Check fun x : PROD True True => match x with PAIR _ _ _ _ => 0 end.
(* Elimination of an inductive object of sort Prop is not allowed on a predicate in sort Set *)
```
which would actually be easy to address (see point 2 discussed in item 2 of the next section).

## `SProp`

### `SProp`-truncation
Similarly, let's call `SProp`-truncation the following type:
```
Variant SSquash (A:Type) : SProp := ssquash : A -> SSquash A.
```
whose content can be `match`-eliminated only in a context of type `SProp`.

Then, any inductive or coinductive type declared in `SProp` is intended to be equivalent to the `SSquash` encapsulation of its declaration in `Type`.

If the encapsulated type is itself a `SProp`, it can be eliminated. This is again a subsingleton elimination because there is a primitive syntactic class of subsingleton types having this property by default:
  - the empty inductive type (possibly with indices)
  - any type previously declared in `SProp` (e.g. `SSquash A`)
  - any record of such types, as in the record presentation of `True` or `and`, without recursivity (and since a record, without indices)

In the paper "Definitional Proof-Irrelevance without K", this class is extended to:
  - non-record sigma-types of types in `SProp`
  - inductive types with disjoint indices (sections 5 and 6 of the paper), a priori to be taken in small types, i.e. hsets

As above, if the encapsulated type is not a syntactic `SProp` but only equivalent to a syntactic `SProp`, it can nevertheless be eliminated by using a proxy. For instance, non-record sigma-types of types in `SProp` can be eliminated by first mapping them to their record alternative. Similarly, inductive types with disjoint indices can be eliminated by mapping them to their definition as an `SProp` defined by recursion on the indices. Avoiding a proxy in these cases is the purpose of points 1 and 3 below.

Proofs of types of `SProp` are definitionally undistinguishable and this prevents extending `SProp` with types for which proofs matter (such as `Acc` whose proofs matter for decidability, or types in `HProp` for which belonging to `HProp` is undecidable).

We may want `match` on arbitrary elements of inhabited `SProp` to automatically reduce. This is the question of implementing eta-expansion for positive types and it is addressed elsewhere.

### Late detection of `SProp`

Actual `SProp` has no template polymorphism. Its subsingleton elimination is restricted to `False` so that dynamic computation of subsingleton elimination does not matter.

We do not recommend template polymorphism for `SProp` (since template polymorphism is already planned to be superseded with universe polymorphism).

In particular, we do not plan late detection of a parametric type in `Type` as an `SProp` liable to be considered impredicative. Late detection of a parametric type in `SProp` as a type supporting subsingleton elimination is the purpose of point 2 (once points 1 and 3 are achieved).

## Subtyping of `SProp` in `Prop`

The types characterizing the class `SProp` are all in `Prop`. This suggests that we could have `SProp` considered a subset of `Prop`. This is difficult to implement and the alternative is to define the following explicit subtyping which takes benefit of `SProp` being recognized as a subset of `Prop` in the class defining `Prop`:
```
Inductive Box (A:SProp) : Prop := box : A -> Box A.
```
Eventually, it would be convenient to have `SProp` implicitly a subtype of `Prop`.

In particular, this would allow to have `False`, `True`, `and`, `ex` systematically put in `SProp` by default and stop distinguising betwen a definitionally proof-irrelevant copy in `SProp` and an equivalent copy missing explicit definitional proof-irrelevance in `Prop`.

# Detailed design for the `Prop` and `SProp` extensions

## Uniformizing the treatment between `Prop` and `SProp`

1. accept singleton types with all arguments in `SProp` to be in `SProp` as it is the case for `Prop`, the only difference being that recursive arguments are excluded; the indices should be in small types (i.e. `Prop` or `Set`)

## Dynamically recognizing subsingleton elimination for `Prop` and `SProp` in `match`

2. This would require calling the subsingleton elimination checker dynamically when typing `match`.

## Generalize the syntactic criterion for being in `Prop` or `SProp`
 
3. accept in `SProp` and `Prop` types with several constructors when (small) indices justify that the constructors are disjoint (section 5 of "Definitional Proof-Irrelevance without K")

# Detailed design for the `HProp` addition

Belonging to `HProp` is not decidable, so exactly characterizing `HProp` requires user-provided data.

There are two solutions:
- either we retarget `Prop` to include `HProp` (simpler)
- or we keep `Prop` as it is and add a new subuniverse `HProp` (less change of habits)

Both solutions follow the same way. Below, we assume the latter. To get the former, just use `Prop` instead of `HProp`.

We shall avoid relying on template polymorphism. However, we may consider a `cast` of the form:
```
(t : HProp by p)
```
which forces the type-checker to recognize a type as being in a smaller universe than decidably detectable.

The status of casts in the implementation is however fragile, so this may require some clarification of casts first.

## New command to support arbitrary `HProp`

We propose a new command:
```
Subsingleton id context : ishProp A := proof.
```
which recast the type of `A` from `context -> Type` to `context -> HProp` so that it is latter considered impredicative.

An alternative is to have a modifier to definitions in the form:
```
Subsingleton id context := def : HProp by proof.
```
But then, we probably want also:
```
Subsingleton id context := def : Hprop.
Proof.
the proof of being hProp
Qed.
```
which may be complicated.

If `HProp` is made distinct from `Prop`, new declarations `Inductive ... : ... -> HProp` would be accepted too. When to tell that the type has subsingleton elimination? There is a proposal in the next section.

## Dynamic detection of subsingleton elimination

We propose an extension of `match` of the following form:
```
match t as id in I params return typ by u with
| C1 vars => body
...
| Cn vars => body
end
```
where, when `I` is `HProp`-truncated but the instance `I args` is an `HProp` proved by `u : forall x y:I args, x = y` (where `I` is temporarily considered in `Type` for the time of the proof), the elimination to `Type` is allowed.

# Side remark on template polymorphism for `Prop`

Instances of parametric types which are not in `Prop` in the general case are automatically recognized as belonging to the `Prop` class (and treated as subsingleton for `match` and as impredicative in function types) when the parameters are themselves in `Prop`. This is typically the case of `prod A B` which behaves as `and A B` when `A` and `B` are in `Prop`.

Template polymorphism induces a view where an inductive type in `Prop` does not necessarily mean explicitly `Prop`-truncated. It is so only when the original type is not a syntactic `Prop`-subsingleton.

Without template polymorphism, explicit coercions from `prod A B` to `and A B` should be inserted (when `A` and `B` are `Prop`), and explicit Prop-boxing of `prod A B` should be done to make `prod A B` behave impredicatively.

# Issues with extraction of `HProp`

Types in `HProp` which are not in the current syntactic class `Prop` could simply be extracted as if they were in `Type`.

# Conclusion

A few extensions could be done pretty easily to avoid the manual use of proxys:
1. accept singleton types with all arguments in `SProp` to be in `SProp` (`True`, `and`, ...)
2. dynamically recognize subsingleton elimination for `Prop` and `SProp` in `match`

The "disjoint indices" extension would require some days of work:

3. accept in `SProp` and `Prop` types with several constructors when (small) indices justify that the constructors are disjoint (section 5 of "Definitional Proof-Irrelevance without K")

The support for `HProp` distinct from `Prop` would require introducing the new subuniverse `HProp` at many places of the code and may be costly.

However, scaling `Prop` to `HProp` would only require the new independent commands:

4. `Subsingleton ...`
5. `match ... by p with ... end`
6. `(t : HProp by p)`

and each of them are worth a design discussion.

A proper inclusion of `SProp` in `Prop` preventing useless duplications of `True`, `False`, `and` and `ex` is to be discussed elsewhere. Eta for `match` on `Prop`/`SProp` types is also to be discussed elsewhere.

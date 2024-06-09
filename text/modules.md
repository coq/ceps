- Title: Addressing a few limitations of the module system

- Author: Hugo Herbelin

----

# Summary

The module system of Coq has several roles:
- name space management and visibility (`Module`, `Import`, `Export`, qualified names)
- modular development of theories (modules parametric over module specifications, `:`, `<:`)
- building of large theories by combination (`with`, `<+`, `Include`)
- sealing of an implementation under an interface for the purpose of extraction towards the OCaml module system (`Module M:T:=S`)

Though inherited from the OCaml module system, it differs from the latter by the absence of syntactic differences between interfaces and implementations. In Coq, types are terms, interfaces can have arbitrary kinds of definitions, and implementations can have axioms.

This CEP tries to address a few limitations of the module system:
1. identifying modules canonically defined by their implementation and modules canonically defined by their interface
2. giving direct access to implementations sealed behind interfaces without going through extraction
3. integrating ideas inherited from OCaml's module system
4. providing more algebraic combinators to build theories

# Propositions

## Towards identifying modules canonically defined by their implementation and modules canonically defined by their interface

Despite the absence of syntactic differences between interfaces and implementations, Coq maintains a somehow artificial distinction between a (so-called) "declared" module, that is a module characterized by its interface and whose implementation is canonically defined to be the same as the interface, and a "defined" module, that is a module characterized by its implementation and whose interface is canonically defined to be the same as the implementation. Here are examples showing the limitation:
- In extraction:
  ```coq
  Require Import Extraction.

  Module M. Definition a:=0. End M.
  Extraction M. (* ok *)

  Module Type T. Definition a:=0. End T.
  Declare Module N : T.
  Fail Extraction N. (* currently unsupported *)
  ```
- In module definitions:
  ```coq
  Module M. Axiom a:nat. End M.
  Fail Module N := M with Definition a:=0. (* "with" not allowed for modules *)

  Module Type T. Axiom a:nat. End T.
  Fail Module N := T with Definition a:=0. (* T not a module *)

  Declare Module N : T with Definition a:=0. (* ok *)
  ```
  even though all three declarations basically build the same module.

  Note: the syntactic limitation of the first case is addressed in [#11897](https://github.com/coq/coq/pull/11897).

In the implementation, these limitations come from the difference between `MExpr(params,expr,None)` (= a module with interface canonically identified with the implementation) and `MType(params,expr)` (= a module with implementation canonically identified with the interface). This difference goes to `module_body` by giving either the value `FullStruct` or the value `Abstract` to the field `mod_expr`.

Both issues would be solved by identifying the two constructions (i.e. rebinding `MType(params,expr)` to `MExpr(params,expr,None)`) and identifying `FullStruct` and `Abstract`.

## Giving direct access to implementations sealed behind interfaces without going through extraction

In Coq, only the interface of a module is relevant for typing a development dependent on a module. In particular, sealing implementations behind interfaces definitely prevents being able to access the contents of an implementation. The latter is then be seen only by extraction which can export the implementation to a programming language, such as OCaml, Haskell, Scheme, etc.

But the implementation is still there!

The proposal is to provide a command `Magic Eval reduction in term` which evaluates `term` by referring to the implementation of the modules mentioned in `term` rather than to their interface. For instance, in:
```coq
Module Type T. Axiom f:nat->nat. End T.
Module N:T. Definition f:=Nat.pred. End N.
```
calling `Magic Eval compute in N.f 1.` would produce `0`.

## Ideas inherited from OCaml's module system

OCaml has two module system features which Coq does not have:
- Private inductive types
- Axiomatic variant of `Module Type` providing a polymorphically-typed module system

## Providing more algebraic combinators to build theories

A force of the module system is to build new theories by combination, resulting in virtually very large theories. I wonder whether modules should not internally be kept as algebraically as possible. Functor application and updating with `with` are kept algebraically, but shouldn't `Include` and `<+` be kept also algebraically and their expansion into a pair of structures (i.e the pair of the expansion of the implementation and of the expansion of the interface) being done lazily.

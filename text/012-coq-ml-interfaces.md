CEP: Roadmap for Public OCaml Interfaces.
-----------------------------------------

- Driver: Emilio J. Gallego Arias (@ejgallego),
  _co-drivers proposed by Emilio_: Pierre-Marie Pédrot (@ppedrot), Hugo Herbelin (@herbelin), Maxime Dénès (@maximedenes), Théo Zimmerman (@Zimmi48) We would like to thank Gabriel Scherer (@gasche) (who of course would be very welcomed to as a co-driver)
- Status: Request For Comments, Preliminary Implementation
- Version: 0.1 (25/04/2017)

----

**Summary**: The goal of this CEP is to streamline Coq's public `.mli`
  files, in particular those related to data-access and
  user-interfaces. Long terms goals are:

- provide a consistent API and naming experience,
- support a systematic, generic CRUD API for core data objects,
- consolidate the main Coq's AST into an extensible and
  editor-friendly format.
- make UI-facing datatypes friendly to serialization towards common
  formats (JSON, SEXP).

The implementation of this CEP should have good effects on the size of
the codebase, remove code duplication, and downsize the API
considerably while at the same time providing extended functionality.

At a minimum, the implementation of this CEP would span along two Coq
releases:

## 8.7: AST revamp

Coq's current AST is quite heavy and makes advanced interaction with
UI difficult or impossible. In particular some of the use cases outlined in
https://github.com/coq/ceps/blob/master/text/009-unified-pretty-printing.md
are hard due to the way Coq's AST process work.

The two main aspects to improve are:

- _AST regularity_: getting information about simple properties of the
  AST requires the UI to know all the details of the AST and the shape
  of the constructors. Code refactoring is also hard, as for instance,
  location or comment preservation require to analyze one case for
  each constructor versus a generic one.

- _syntax manipulation_: a UI may want to understand how syntax is
   transformed. For instance, it is very useful to compare a term with
   interpreted notations with the original one; similarly for implicit
   arguments. However, Coq will use a different datatypes for
   elaborated syntax which greatly complicates the diffing algorithm.

We propose to improve Coq wrt these properties by evolving the current
AST towards an attribute-based, single polymorphic representation
designed for easy comparison and manipulation.

### Example use cases:

- **Mapping terms to locations:** UI can map locations to terms and
  vice-versa without having to understand the full
  AST. Folding/unfolding or terms, references.

- **Notation / impargs unfolding:** UI have access to notation and
  implicit arguments resolution / re-insertion.

- **Attributes**: Generic support for attributes on particular AST
  nodes; ensure attribute preservation by transformations.

- **Developer friendliness:** Extensible OCaml API wrt to new
  attributes, node types, or syntax extensions. Make attributes
  transparent for the non-interested developer.

### Phase I: attributes / generic AST

The first step is to introduce in Coq the notion of "generic" AST
node. This is done in coq/coq#402 using private records, and
significant improves the quality of our AST API.

More information can be found in the PR itself and in the developer
documentation, but the main idea is to introduce a type:
```ocaml
(** Generic metadata for AST nodes *)
type 'a ast = private {
  v   : 'a;
  loc : Loc.t option;
  att : ...
}
```

and define AST as:
```ocaml
type constr_expr_n =
| CRef ...
and constr_expr = constr_expr ast
```

Attributes can be accessed with regular record pattern-matching `{ v;
loc }` and nodes are created using constructors `CAst.make ?loc ?att
obj`.

**Challenges:** This is a foundational patch and it was quite hard to
  get right. Current status is good, however, small-scale API
  evolutions are to be expected as developers try to use the new
  interfaces.

**Upsides:** Improves API significantly, making it more robust wrt
  future changes and generic wrt to locations/attributes. Enables
  several use cases; makes the serialization output much more usable
  by UI. Using records for AST nodes.

**Downsides:** Will break plugins accessing the AST. However porting
  is trivial. In order to minimize the diff size of the PR, some paths
  are not fully optimized, which has very minor impact on front-end
  performance. In our opinion, optimization here is not worth it as
  Phase II should greatly improve this aspect.

### Phase II: `constrexpr` + `glob_constr` ≡ `coq_expr`

Currently, Coq represents untyped terms using two different
representations,
[`constr_expr`](https://github.com/coq/coq/blob/trunk/intf/constrexpr.mli#L69),
which is the parsing AST, and
[`glob_constr`](https://github.com/coq/coq/blob/trunk/intf/glob_term.mli#L33),
a more canonical representation where identifiers have been resolved,
notations interpreted, and implicit arguments inserted. Some other
minor processes are performed.

The step that transforms a `constr_expr` into a `glob_constr` is named
_internalization_. It is a complex process, intertwining the
transformations outlined above. The reverse step is called
"externalization", and it is only used for printing, producing
different ASTs for different printing flags.

**Analysis:** Structurally, both untyped representations are extremely
similar. The main differences are:

- _References_, which are resolved in `glob_constr`.
- _Abstractions_, which support list of binders in `constr_expr`.
- _Patterns_, structurally the same, `glob_constr` resolves some information about them.
- _Recursive definitions_, `glob_constr` uses a single entry vs two for `constr_expr`.
- _Application_, `constr_expr` provides two forms, for implicit and explicit.
- _Syntactic Sugar_, `constr_expr` includes notations, records, and delimiters.

It is worth noting that `glob_constr` seems to lose quite a bit of the
location information present in the original AST, this proposal would
remedy that.

**Unification:**

The idea to unify both data types is to first reduce some arbitrary
differences, then capture the differences via
_type-parameters_. Differences in _abstraction_, _recursive
definitions_, and _application_ belong to the first category.

The rest would give us a unified type:

```ocaml
type ('var, 'case, 'syn, 't) coq_expr_n =
| Ref of 'var
| ....
| Syntax of 'syn
and ('var, 'case, 'syn, 't) coq_expr = coq_expr_n ast
```

Then, we can define our old types using regular recursive types:
```ocaml
type parse_expr = (pvar, pcase, psyntax, parse_expr) coq_expr
type resolved_expr = (global_reference, pcase, psyntax, resolved_expr) coq_expr
type core_expr = (global_reference, rcase, unit, core_expr) coq_expr

```
and our transformations:
```ocaml
resolve_refs : parse_expr -> resolved_expr
```
being instances of the same type, the process makes them comparable
and attribute preservation is automatic.

See below for a detailed todo-plan.

**Challenges:** This is a difficult and challenging patch touching
  many core parts of the Coq frontend. The benefit is great but the
  effort to reach here will also be. The main challenge likely lies in
  getting all the small details right. There are some very subtle
  things happening in internalization that we'd need to account for.

**Special Challenge:** Unfortunately Coq's AST is not a pure algebraic
  datatype due to:
```ocaml
| CHole of Evar_kinds.t option * intro_pattern_naming_expr * Genarg.raw_generic_argument option
```
  This is used to enable `ltac:(tactic)` expressions, which will be
  translated to a hole with an attached tactic. Unfortunately this
  dynamic typing really limits the implementation of a modular
  approach: the generic interpretation handler has to be aware of all
  our passes and interact properly with them.

  There exists several solutions to this problem, however it is yet
  unclear how to proceed.

**Upsides:** Having a common format would clean up large parts of the
  front-end and remove many boilerplate code. UI and plugins could
  work with a single tree and enable syntax manipulations on the fly,
  and it would be easier to extend the AST with some new syntactic
  features.

**Downsides:** If we chose a modular pass architecture it could be the
  case the we end up being slightly slower than the current
  approach. However, the patch should bring some other performance
  benefits, so the impact is hard to predict. Printing should become
  much faster in some cases. Overall, the impact in the frontend
  should be small enough for the modular architecture to be worth it.

### Detailed analysis of the unification.

- _References_:

 | `constr_expr` | `glob_constr` |
 |---------------|---------------|
 | `CRef of reference * instance_expr option` |  `GRef of (global_reference * glob_level list option)` |
 | | `GVar of Id.t` |

There are several options here, we could use a sum datatype for the
`glob_constr` case, or we could add `CVar` to the AST.

- _Recursive definitions_:

We have `CFix|CCoFix` vs `GRec`. Indeed there are more things uniting
them than dividing them, however the structure of `GRec` seems
a bit suspicious, so we may like to use a 3rd way.

Anyways, experimental evidence shows that resolving this is easy and
the unification proceeds quite straightforwardly.

- _Abstraction_:

 | `constr_expr` | `glob_constr` |
 |---------------|---------------|
 | `CLambdaN of binder_expr list * constr_expr` | `GLambda of Name.t * binding_kind *  glob_constr * glob_constr` |

This one is more tricky, however I wonder if the first case is worth
it or we should unfold from the start. Note that nested binder
structure is lost when printing anyways:

```coq
Definition ex := fun (n : nat) => fun (m : nat) => n + m.
Print ex.
ex = fun n m : nat => n + m : nat -> nat -> nat
```

- _Application_:

 | `constr_expr` | `glob_constr` |
 |---------------|---------------|
 | `CAppExpl of (proj_flag * reference * instance_expr option) * constr_expr list` | `GApp of glob_constr * glob_constr list` |

This requires a bit of tweaking but should be straightforward.

- _Pattern Matching_:


- _Syntax extensions_:

  `CNotation of notation * constr_notation_substitution`

## 8.8: CRUD and Serialization

The **C**reate **R**ead **U**pdate **D**elete paradigm tries to
provide a systematic API for the management of objects of interest. In
the context of Coq, this is of particular interest for user interfaces
and analysis tools. It is common for them to ask questions such as
"how many notations are defined?", "which lemmas use that definition",
or "what is the current list of enabled warnings".

Our goal in this second phase is to define a standard interface for
Coq CRUD objects.

### Main use cases:

The main use cases come from UI and proof analysis tools, we can highlight:

- **Coq files as a data source:** using the standard interface, it
  becomes easy to expose coq files a standard database, which can be
  queried using standard languages.
- **IDE integration:** UI can now offload knowledge about Coq objects
  to queries, and allow the user to explore developments in a friendly way.
- **Developer friendliness:** A single central interface means a
  smaller API and faster learning curve to plugin developers.
- **Candidates:** Options, Notations, Goals, Library / Environment,
  Warnings, Errors Messages, Messages, Modules... all those are first
  candidates to the put under the common CRUD API.
- **Subscription:** In many cases clients would like to be subscribed
  to events related to object lifetime. This model would allows to
  extend the current feedback model to a more granular view.

**Challenges:** There are no particular challenge other than
  establishing a namespace for objects, but given the nature of Coq a
  simple system would do. More research on the proper technical
  implementation for the CRUD instance mechanism is be needed, but
  some form of existential types seem like the obvious choice.

**Upsides/Downsides:** The upsides are clear, the main downsides would
  be the cost of API changes, but this could be alleviated by a
  deprecation process in most cases.

## Alternatives

Not other alternatives known at the moment.

- Title: Threading the state in the implementation
- Driver: Hugo
- Status: Draft

# Summary and motivation

Coq keeps internal data in tables updated by side effects. Several bugs or hacks come from the difficulty to control the flow of these side effects. This ceps proposes some directions to thread tables updating in a purely functional way.

# Current structure of state in Coq

All global tables are registered to `summary.ml` and `Summary.freeze_summaries : marshallable -> Summary.frozen`, to a few exceptions:
- The list of entries of a document is in `Lib.lib_state` and not registered as a summary
- The list of open goals is in `Proof_global.pstates : Proof_global.t` and is not synchronized

The combination of all summaries and `lib_state` is called `States.state`. The combination of `States.state` and `Proof_global.t` is in `Vernacstate.t`. It can be thought as _the_ global state of Coq.

# General proposal

## State-passing-translation / environment-passing-translation

The proposal is to differentiate between two kinds of functions.
- Functions manipulating the state generically shall be "state-passing-translated" (or "environment-passing-translated" depending on need) over the type `States.state`
- Functions morally manipulating only a reduced number of components of the global state shall be "state-passing-translated" (or "environment--passing-translated" depending on need) over an ad hoc subset of `States.state` (e.g. `printing_state`, or `typing_state`, or `tactic_state`, ...)

## Registering of tables/summaries

The proposal is to reverse the model of registration of a table. Instead of declaring a local mutable object to the summary manager by sending to it read/write/init methods (in practice called `freeze`/`unfreeze`/`init`), we ask the summary manager to send us read and modify methods on the global state (so-called "lenses" as far as I understood).

# Key components managing states

## Declaring a global table: `declare_summary`

We shall rename `Summaries.frozen` into `Summaries.summaries` to hightlight that it is not anymore a "freeze", but _the_ (functional) summary of all tables.

We shall provide instead a registration method (see #8624)
```
val declare_functional_summary : name:string -> 'a -> 'a Dyn.tag
```
which shall return a tag allowing to use the following methods:
```
val project_from_functional_summary : summaries -> 'a Dyn.tag -> 'a
val lift_functional_summary : 'a Dyn.tag -> ('a -> 'a) -> summaries -> summaries
```

Note: Eventually, the infixed `functional` will be dropped. It is made explicit for the time of the transition to happen.

## Declaring a document object: `declare_object`

We shall similarly provide a functional form of `declare_object` to declare a new kind of document entry (e.g. `Notation`, `Hint`, `Axiom`, ...)
```ocaml
val declare_functional_object :
  ('a,'b) functional_object_declaration -> 'b Dyn.tag -> ('a -> 'b obj)
```
where the key registered methods are moved from the non-functional
```ocaml
type 'a object_declaration = {
  object_name : string;
  cache_function : object_name * 'a -> unit;
  load_function : int -> object_name * 'a -> unit;
  open_function : int -> object_name * 'a -> unit;
  classify_function : 'a -> 'a substitutivity;
  subst_function :  substitution * 'a -> 'a;
  discharge_function : object_name * 'a -> 'a option;
  rebuild_function : 'a -> 'a
}
```
to the functional:
```ocaml
type ('a,'b) functional_object_declaration = {
  object_name : string;
  cache_function : object_name * 'a -> 'b -> 'b;
  load_function : int -> object_name * 'a -> summaries -> summaries;
  open_function : int -> object_name * 'a -> summaries -> summaries;
  classify_function : 'a -> 'a substitutivity;
  subst_function :  substitution * 'a -> 'a;
  discharge_function : object_name * 'a -> state -> 'a option;
  rebuild_function : 'a -> state -> 'a
}
```
The `load` and `open` methods are used by `Require` and `Import` respectively. They are called generically, so, they have to apply to the generic collection of summaries.

The `discharge` and `rebuild` method sometimes need to look at the current state (e.g. in `typeclasses.ml`, so we pass them the global state for reading.

The `cache` method is typically used by `add_anonymous_leaf`. We give it an object specific type `'b` so that modular states can be used.

The type `obj` has been changed here to `'b obj`. The `'b` shall be the type of the table used by the object. E.g., for implicit arguments, it shall be `implicits_list list GlobRef.Map.t`.

Note: this could be a good time to rename `load` to `require` and `open` to `import` to make code more readable??

## Importing a module: `Lib.open_objects`, `Declaremods.cache_object`

The first one shall be moved from
```
val open_objects : int -> Libnames.object_prefix -> lib_objects -> unit
```
to
```
val open_objects : int -> Libnames.object_prefix -> lib_objects -> summaries -> summaries
```

## Loading a module: `Lib.load_objects`, `Declaremods.load_module`, ...

The first one shall be moved from
```
val load_objects : int -> Libnames.object_prefix -> lib_objects -> unit
```
to
```
val load_objects : int -> Libnames.object_prefix -> lib_objects -> summaries -> summaries
```

## Caching an object: `Lib.add_anonymous_leaf`

To get state modularity, we shall move its type from:
```
val add_anonymous_leaf : ?cache_first:bool -> Libobject.obj -> unit
```
to
```
val add_anonymous_leaf : 'b obj -> 'b * lib_state --> 'b * lib_state
```
It will then be the responsibility of the caller to thread the `lib_state` and to eventually inject the individual state in the global state (at latest in the main `Vernacentries.interp` loop which, because it is the interpreter of all kinds of command, can only work on `Vernacstates.t`)

## Goal state

So that a goal can evolve compartmentalized (with its local state of definitions when calling `abstract`, or with a local state of implicit arguments and notations), a private global state should be attached to goal.

This global state could be a field in `Proofview.Goal.t` but it seems that it would be more interesting to have it as a field of the `evar_map`. Since the latter is already threaded, we would get the threading for free. This would also provide an alternative for free to #8598.

## STM

What are the expectation of the STM in terms of state threading?
 
# Examples of issues to be solved by a functional state

## Term printing

Basically all commands or tactics potentially need to to report about errors and for that, either to print terms or to raise an ad hoc exception. In both cases, they need to know the current state so that the message is printed/reported in the appropriate state.

Generalizing the `evar_map` so that it includes at least the printer state would allow to fix this for all errors which already include the evar map.

Note: the `process_vernac_interp_error` hack turns interpretation error (`TypeError`, `PretypeError`, ...) into `Pp.t`. We currently need it to be called before changes to the global state because otherwise the printer may try to print object which do not exist any more in the modified global state. This introduces complications: some commands changing state (e.g. the mechanism of obligations) have to call it preventively. Some bugs, e.g. #4781, are related to this. `process_vernac_interp_error` would not be anymore necessary with errors closed with respect to the environment needed to interpret them. 

## Goal state

There are problems with `abstract` (#3608) with a confusion between the goal state referring to its inner env or to the global env, as well as other summaries being only outside. E.g. printing `foo_subproof` may require to look for implicit arguments which are currently registered only outside the goal.

We may want to use notations, or implicit arguments locally to a goal and this is not possible by lack of a state attached to a goal state.

## For the record, a possibly related bugs

Hint declaring functions mess with the global state (#8118).

# A key question

Who wants to participate to this project?

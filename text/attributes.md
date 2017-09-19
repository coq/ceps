Generic attribute syntax
========================

Arnaud Spiwack

This document describes a proposal to add a generic syntax to qualify
Coq's toplevel declarations.

### Acknowledgment ###

Original idea from Pierre-Marie Pédrot.

Why?
----

Toplevel declarations can have a number of qualifiers such as:

```coq
Local Polymorphic Program Definition foo …
```

And more are coming (_e.g._:
[#79](https://github.com/coq/coq/pull/79)). The current approach,
which hard-codes these qualifiers in the parser is rather unwieldy:

- The order in which the qualifiers must be provided is fixed:
    ```coq
    Polymorphic Local Program Definition foo …
    ```
    is not a valid declaration.
- Adding a qualifier is pretty involved. `It involves
  [a monolithic environment-passing recursive function](https://github.com/coq/coq/blob/57a3f38832dba3a9b7a1de146bd45451227a03e8/toplevel/vernacentries.ml#L2007-L2011). It
  is easy to create a syntax which breaks the parser (discussion in
  [#79](https://github.com/coq/coq/pull/79) provides an example).
- Plugins cannot modify Coq's parser that deeply hence are limited to
  creating new toplevel declarations, no new qualifiers.


What?
-----

To remedy these issues, our proposal is to add a generic syntax for
qualifiers called _attributes_. This results in a modification of the
parser once and for all with the following requirements:

- Attributes form a set: the order in which they are written by the
  user don't matter.
- The implementation of toplevel declarations will have an entry point
  for plugins which use the attributes to modify the declaration.
- Each toplevel declaration may use some of the attributes natively.
- Attributes which have not been used either natively or by a plugin
  will raise a warning, to facilitate catching typos.
    - Making it a non-fatal failure makes it easier to make a plugin
      optional or to write Coq files which are valid between versions.
    - In a future version of Coq it will presumably be possible to
      turn warnings into errors.

How?
----

The use of attributes to extend the capabilities of a language and
enable plugins has been demonstrated with a great variety of
applications by some modern languages (like Rust, from the design of
which this proposal is largely inspired).

### Syntax ###

We propose the following syntax which is inspired from existing the
syntax of notations as well as the
[equations](https://www.irif.univ-paris-diderot.fr/~sozeau/research/coq/equations.en.html)
plugin.

```coq
Definition (attr0, attr1(attr10,attr11), …) name := …
```

(And similarly with `Lemma`, `Theorem`, `Fixpoint`, etc…). The
attributes, such as `attr0`, are passed as a set of mere strings to
the plugins (but we still have syntax errors in the form of the unused
attribute warning).

Attributes such as `attr1` recursively contain a
set of attributes. This is more convenient (but not more expressive)
than having a bunch of attribute `attr1_attr10`,
`attr2_attr20`. Therefore an "attribute set" is really a map from
attributes (string) to attribute sets (a facility shall be offered to
extract an attribute from an attribute set while validating that it
has no sub-attributes). The syntax `attr1()` is equivalent to `attr1`.

### Entrypoint for plugins ###

Toplevel declarations will be equipped with a hook, in which a stack
of plugins can be registered. The plugins will receive an attribute
set and a `vernac_expr` and will return a modified `vernac_expr` and a
modified attribute set for the next plugin (last registered plugin
acts first, Coq's native use of attributes comes last).

It is the responsibility of the plugins to return an accurate
attribute set (in particular not removing from the attribute set
attributes it does not know about).

### Compatibility ###

The existing qualifiers (`Program`, `Polymorphic`, etc…) will be
converted to (natively interpreted) attributes.
To preserve backward compatibility the existing syntax for qualifiers
will become sugar for these new attributes.

Discussion
----------

### Program ###

One of the benefit of this attribute proposal is that it may help with
a long-standing user request: separate the various features of
Program. At least it can address the syntax that such an extension
would have (it cannot, of course, address the engineering challenge of
disentangling the feature in Coq's implementation).

- `Definition (program) foo := …` would activate Program in its
  totality (it would behave like the current `Program Definition foo
  := …`)
- `Definition (program(subtypes)) foo := …`, `Definition
  (program(match)) foo := …` would only only activate, respectively,
  the special treatment of Σ-types and the special pattern-matching
  compilation.
- A special `Definition (program(obligations))` could also be defined
  where the normal pretyper would be used, except it would prompt for
  proof obligations.

#### Further discussion ####

An alternative design could be to allow negative elements in attribute
sets. For instance with the syntax `!attr` (borrowed from Rust). In
which case, we would not use `subtypes` and `obligations` to add from
program and special-case the empty `program` as containing all the
features. Instead we would _take away_ feature from program, for
instance:

- `Definition (program(!match))` would deactivate the compilation of
  pattern-matching in Program (which would be equivalent to what we
  wrote `program(subtypes)` above)

The two designs are not incompatible. We could have an attribute
`program_with` which activates the obligation mechanism plus whatever
is asked of it. That way `program` would be equivalent to
`program_with(subtypes,match)` and `program(!match)` to
`program_with(subtypes)` (this also eliminates the need for
special-casing a `program(obligations)` as above).

### Local (de)activation of scheme generation ###

A pattern which is not uncommon, in Coq, is to use something along the
following line:

```coq
Unset Elimination Scheme.
Inductive foo := …
Set Elimination Scheme.
```

Toggling of global flags in order to get a local behaviour can be
rather clumsy. Instead, the same pattern could use attributes. For
instance, using the negative attribute syntax suggested in the Program
section:

```coq
Inductive (!induction_scheme)
```


### Attributes on expressions ###

Ocaml makes it possible to attach attributes to any expression. This
allows further expressiveness such as controlling type-based code
generation and local instrumentation. While this has been
demonstrated, by the Ocaml community to be very useful, it is
mostly orthogonal to the present proposal: attaching attributes to
toplevel declarations and to expressions act on distinct parts of the
code base and address different features.

For the features described in this proposal, toplevel declarations
seem to be the appropriate place to act. This is why we focused, in
this proposal, on associating attributes to declarations.

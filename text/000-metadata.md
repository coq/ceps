- Title: Adding MetaData to Coq

- Drivers: @CohenCyril @palmskog @gares @TDiazT @pi8027 @ejgallego @SkySkimmer

----

# Summary

The purpose is to add several kind of metadata, attached to constants,
modules, files, etc.


# Motivation

This metadata should be usable and used to enhance search,
documentation generation, and build database for Coq libraries.


# Detailed design

## For search

- adding docstrings (that search can grep inside)
  ```coq
  #[docstring="foo is a dummy lemma"]
  Lemma foo : True. by []. Qed.
  ```
- aliasing of statements so that search can find a statement which is
  convertible but not syntactically equal.
  ```coq
  #[alias="forall x y, x * y = y * x"]
  Lemma mulrC : commutative mul. ...

  Search (_ * _ = _ * _). (* mulrC appears *)
  ```
  or
  ```coq
  #[alias(unfold="commutative")]
  Lemma mulrC : commutative mul. ...
  ```
  and we could have several aliases (`#[alias=..., alias=..., ...]`).
- Give a name from the litterature (searchable again)
  ```coq
  #[name="Abel-Ruffini Theorem", name="Abel's Theorem"]
  Lemma unsolvable_quintic : ...
  ```
- Have a way to refer to a bibliography from a definition or its proof
  E.g via a `#[ref="name"]` attribute with a bibtex (for example),
  shared accross one or several projects.

# Drawbacks

TODO

# Alternatives

TODO

# Unresolved questions

Where to store this?
TODO

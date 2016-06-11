- Title: Namespaces

- Drivers: Jason

- Status: Draft

----

# Summary

This document descibes a proposal to satisfy
[feature request #4455](https://coq.inria.fr/bugs/show_bug.cgi?id=4455) and
[feature request #3171](https://coq.inria.fr/bugs/show_bug.cgi?id=3171) and solve
[JasonGross/coq-tools#16](https://github.com/JasonGross/coq-tools/issues/16)
by giving Coq a better notion of namespaces.

The idea is that users should be allowed to declare that certain constants should have user-chosen
kernel names.

# Syntax

The following are typical examples:
```coq
Namespace Coq.Init.
  Module Datatypes2.
    ...
  End Datatypes2.
End Coq.Init.
```

```coq
Local Namespace Init.
  Module Datatypes.
    ...
  End Datatypes.
End Init.
```

# Semantics

Roughly, `Namespace`s act like directories in the file tree.

- Any object `Z` inside a (global) namespace `A.B...C` shall have the kernel name `A.B...C.Z`.
- Any object `Z` inside a (local) namespace `A.B...C` in a module/namespace `F.G...H` shall have the kernel name `F.G...H.A.B...C.Z`.
- A `Global Namespace` command shall be exactly the same as an unqualified `Namespace` command
- `Namespace`s, unlike `Section`s and `Module`s, *must* permit duplication; it is not an error to write
```coq
Namespace Coq.Init.
  Module A.
  End A.
End Coq.Init.
Namespace Coq.Program.
  Module B.
    Require Import Coq.Init.A.
  End B.
End Coq.Program
Namespace Coq.Init.
  Module C.
    Require Import Coq.Program.B.
  End C.
End Coq.Init.
```
- Nesting global `Namespace`s shall emit a warning like `Warning: Namespaces declare absolute prefixes.  The innermost namespace dominates any outer namespace.  Use Local Namespace to nest namespaces, or use Global Namespace to suppress this warning.`
- It shall be an error to use a `Namespace` inside a Functor, a `Module Type`, a `Section`, or a `Proof`.  It shall not be an error to use `Namespace` inside an unparameterized `Module`.
- At the disgression of the implementor, objects inside `Namespace`s may be restricted to `Module`s, or to any set of objects which include `Module`s.

# Consistency Concerns

The kernel must check that no two objects (`Module`s, `Definition`s, etc) have the same kernel name, and issue an `inconsistent assumptions over` error message if declaring a definition or importing a file yields two objects with the same kernel name.
As a side-effect, this should robustly guard against the recent proofs of `False` discovered by [Maxime Dénès](https://github.com/maximedenes).

## Changes
* 2016-07-10, first draft

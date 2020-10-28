- Title: Packaging coq with native_compute

- Drivers: Erik Martin-Dorel (**@erikmd**), Pierre Roux (**@proux01**)

----

# Motivation

Currently, the use of `native_compute` in libraries involving many dependencies is [inconvenient](https://github.com/coq/coq/issues/12564#issuecomment-647546401) (so that nobody actually uses this feature). Indeed, all their dependencies need to be recompiled with the `-native-compiler yes` option passed to `coqc`. And this needs to be done in a specific way for each dependency, depending on the build system it uses (see e.g., [the doc of `coq_makefile`](https://coq.inria.fr/refman/practical-tools/utilities.html#precompiling-for-native-compute)), if possible at all.

The overall aim of this proposal is to provide an `opam` meta-package (named e.g. `coq-native`) that users can install to automatically (re)compile everything with `native_compute` (no need for a manual `opam pin edit`).

# Summary

This CEPS offers a new strategy for setting the default value for the `-native-compiler` option (in `coqc` and in the `opam` packaging).

The proposed design tackles the following two use cases:

1. Most users' (who don't even want to hear about `native_compute`) preferred behavior would be compiling Coq with `-native-compiler no` by default.
2. `native_compute` users' preferred behavior would be to easily recompile all their libraries with `coqc -native-compiler yes` (while doing this currently with `opam` requires passing custom environment variables (if possible) which aren't the same across the build systems used by libraries, thus making the setup for efficiently using `native_compute` terribly unpractical).

Also, this proposal makes the configuration uniform across the platforms (while `native_compute` [was permanently disabled for macOS](https://github.com/ocaml/opam-repository/pull/16908) to workaround performance issues, cf. [coq/coq#11178](https://github.com/coq/coq/issues/11178)).

# Detailed design

The proposal is three-fold:

1. Update the `coq` packaging in `opam-repository` so that Coq's standard library is compiled with `-native-compiler no` by default, unless an additional meta-package `coq-native` has been installed by the user.
2. Change the default `coqc` option to `-native-compiler on` instead of `-native-compiler ondemand`.
3. Optionally: to enhance `native_compute` support with old versions of Coq (the releases of Coq before the item 2. above is implemented), update the `opam` packacking of the considered libraries.

## Regarding item 1:

* Add an opam metapackage `coq-native.1`:

```
opam-version: "2.0"
maintainer: "Erik Martin-Dorel"
authors: "Coq"
homepage: "https://coq.inria.fr/"
bug-reports: "https://github.com/coq/coq/issues"
conflicts: [
  "coq" {< "8.5"}
]
synopsis: "Dummy package enabling coq's native-compiler flag"
description: """
This package acts as a package flag for the ambient switch, taken into
account by coq (and possibly any coq library) to enable native_compute
at configure time, triggering the generation of .coq-native/* files.

REMARKS:
- you might face with issues installing this package flag under macOS,
  cf. <https://github.com/coq/coq/issues/11178>
- for more details, see <https://github.com/coq/ceps/pull/48>.
"""
```

* Add the following lines in the opam packages of `coq`:

```diff
diff --git a/packages/coq/coq.8.11.2/opam b/packages/coq/coq.8.11.2/opam
index fdb19e9da7..3d3dee7570 100644
--- a/packages/coq/coq.8.11.2/opam
+++ b/packages/coq/coq.8.11.2/opam
@@ -23,6 +23,9 @@ depends: [
   "num"
   "conf-findutils" {build}
 ]
+depopts: [
+  "coq-native"
+]
 build: [
   [
     "./configure"
@@ -33,7 +36,9 @@ build: [
     "-libdir" "%{lib}%/coq"
     "-datadir" "%{share}%/coq"
     "-coqide" "no"
-    "-native-compiler" {os = "macos"} "no" {os = "macos"}
+    "-native-compiler" "yes" {coq-native:installed} "no" {!coq-native:installed}
   ]
   [make "-j%{jobs}%"]
   [make "-j%{jobs}%" "byte"]
```

## Regarding item 2:

The `coqc` option `-native-compiler ondemand` corresponds to the default behavior since [4ad6855](https://github.com/coq/coq/commit/4ad6855504db2ce15a474bd646e19151aa8142e2) (8.5beta3).

See [the tabular of this coq/coq#12564 comment](https://github.com/coq/coq/issues/12564#issuecomment-647464937) for a summary of all behaviors.

With the current codebase, the change will amount to replacing [this line of `toplevel/coqargs.ml`](https://github.com/coq/coq/blob/473160ebe4a835dde50d6c209ab17c7e1b84979c/toplevel/coqargs.ml#L101) with:

```ocaml
then NativeOn {ondemand=false}
```

## Regarding item 3:

Assuming we want to use `native_compute` with `coq-mathcomp-ssreflect` (or any library built with `coq_makefile`), the `opam` file has to be extended like this (see e.g. [Coq's refman](https://coq.github.io/doc/master/refman/practical-tools/utilities.html?highlight=coq_makefile#precompiling-for-native-compute)): 

```diff
diff --git a/packages/coq-mathcomp-ssreflect/coq-mathcomp-ssreflect.1.10.0/opam b/packages/coq-mathcomp-ssreflect/coq-mathcomp-ssreflect.1.10.0/opam
--- a/packages/coq-mathcomp-ssreflect/coq-mathcomp-ssreflect.1.10.0/opam
+++ b/packages/coq-mathcomp-ssreflect/coq-mathcomp-ssreflect.1.10.0/opam
@@ -6,7 +6,8 @@
 dev-repo: "git+https://github.com/math-comp/math-comp.git"
 license: "CeCILL-B"
 
-build: [ make "-C" "mathcomp/ssreflect" "-j" "%{jobs}%" ]
+build: [ make "-C" "mathcomp/ssreflect" "-j" "%{jobs}%" "COQEXTRAFLAGS+=-native-compiler yes" {coq-native:installed}]
 install: [ make "-C" "mathcomp/ssreflect" "install" ]
 depends: [ "coq" { (>= "8.7" & < "8.12~") } ]
```

Doing this, one can notice that the appropriate `.coq-native` directory has succesfully been installed along the `.vo` of the library: 

```bash
find $(opam config var lib) -name ".coq-native" | grep ssreflect
```

# Drawbacks

To fully benefit from `native_compute` with previously released versions of Coq, item 3. is necessary, albeit it should only require some (`opam`) packaging update, which can be performed directly in the <https://github.com/coq/opam-coq-archive> repository.

# Alternatives

N/A

# Unresolved questions

* The implementation of items 1. and 3. above rely on `make`, but how to implement the `dune` counterpart? (Cc **@ejgallego**).

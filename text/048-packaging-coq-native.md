- Title: Packaging coq with native_compute

- Drivers: Erik Martin-Dorel (**@erikmd**), Pierre Roux (**@proux01**)

----

# Motivation

Currently, the use of `native_compute` in libraries involving many dependencies is [inconvenient](https://github.com/coq/coq/issues/12564#issuecomment-647546401) (so that nobody actually uses this feature). Indeed, all their dependencies need to be recompiled with the `-native-compiler yes` option passed to `coqc`. And this needs to be done in a specific way for each dependency, depending on the build system it uses (see e.g., [the doc of `coq_makefile`](https://coq.inria.fr/refman/practical-tools/utilities.html#precompiling-for-native-compute)), if possible at all.

The overall aim of this proposal is to provide an `opam` meta-package (named e.g. `coq-native`) that users can install to automatically (re)compile everything with `native_compute` (no need for a manual `opam pin edit`).

# Summary

This CEP offers a new strategy for setting the default value for the `-native-compiler` option (in `coqc` and in the `opam` packaging).

The proposed design tackles the following two use cases:

1. Most users' (who don't even want to hear about `native_compute`) preferred behavior would be compiling the stdlib **and** subsequent Coq libraries with `-native-compiler no` by default.
2. `native_compute` users' preferred behavior would be to easily recompile all their libraries with `coqc -native-compiler yes` (while doing this currently with `opam` requires passing custom environment variables (if possible) which aren't the same across the build systems used by libraries, thus making the setup for efficiently using `native_compute` terribly unpractical).

Also, this proposal makes the configuration uniform across the platforms (while `native_compute` [was permanently disabled for macOS](https://github.com/ocaml/opam-repository/pull/16908) to workaround performance issues, cf. [coq/coq#11178](https://github.com/coq/coq/issues/11178)).

# Detailed design

The proposal is three-fold:

* **item 1.** Update the `coq` packaging in [ocaml/opam-repository](https://github.com/ocaml/opam-repository) so that Coq's standard library is compiled with `-native-compiler no` by default, unless an additional meta-package `coq-native` has been installed by the user.
* **item 2.** Extend the `./configure -native-compiler` options:
    * option `./configure -native-compiler yes` now impacts the default value of option `coqc -native-compiler` (in order to precompile both stdlib and third-party libraries with `-native-compiler yes`);
	* option `-native-compiler ondemand` (which becomes the default when compiling coq manually) preserves the previous default behavior (modulo the stdlib that is not precompiled anymore).
* **item 3.** Optionally: to enhance `native_compute` support with old versions of Coq (the releases of Coq before 8.13 where **item 2** is implemented), update the `opam` packaging of the considered libraries.


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
synopsis: "Package flag enabling coq's native-compiler flag"
description: """
This package acts as a package flag for the ambient switch, taken into
account by coq (and possibly any coq library) to enable native_compute
at configure time, triggering the installation of .coq-native/* files
for the coq standard library and subsequent coq libraries.

This implements item 1 of CEP #48 <https://github.com/coq/ceps/pull/48>.

Remarks:

1. you might face with issues installing this package flag under macOS,
   see <https://github.com/coq/coq/issues/11178>.
2. this package is not intended to be used as a dependency of other
   packages (notably as installing or uninstalling this package may
   trigger a rebuild of all coq packages in the ambient switch).
3. the option set by this package will be automatically propagated to
   coqc for coq >= 8.13 (but the packaging of coq libraries for
   earlier versions of coq may need an update: for details, see item 3
   of CEP #48 <https://github.com/coq/ceps/pull/48>).
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

The following array, adapted from [this coq/coq#12564 comment](https://github.com/coq/coq/issues/12564#issuecomment-647464937), summarizes all behaviors (the changes are highlighted in bold):

| `configure (<8.13)` | `configure (>=8.13)` | `coqc` | outcome |
| --- | --- | --- | --- |
| *N/A* | **yes** | yes (default if omitted) | `.coq-native/*` + temporary (when calling `native_compute`) |
| *N/A* | **yes** | ondemand | temporary |
| *N/A* | **yes** | no | none |
| yes | **ondemand** | yes | `.coq-native/*` + temporary (when calling `native_compute`) |
| yes | **ondemand** | ondemand (default if omitted) | temporary |
| yes | **ondemand** | no | none |
| no | no | yes | none |
| no | no | ondemand | none |
| no | no | no | none |

Note also that (for `coq >= 8.13`), **the stdlib is only precompiled with `./configure -native-compiler yes`**. It is not precompiled otherwise.
  
[PR coq/coq#13352](https://github.com/coq/coq/pull/13352) implements this item.

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

Doing this, one can notice that the appropriate `.coq-native` directory has successfully been installed along the `.vo` of the library: 

```bash
find "$(opam config var lib)" -name ".coq-native" | grep ssreflect
```

# Note to library developers and package maintainers

To fully benefit from `native_compute` with a library using Coq 8.5+, some (`opam`) packaging update may be required for this library's dependencies:

- for `coq_makefile`: no change required for Coq 8.13+; otherwise follow **item 3** above (related to Section [Precompiling for `native_compute`](https://coq.github.io/doc/master/refman/practical-tools/utilities.html?highlight=coq_makefile#precompiling-for-native-compute) in Coq refman);
- for `dune / coq.theory`: this will require Coq 8.12.1+ and a version of `dune` implementing [PR ocaml/dune#3210](https://github.com/ocaml/dune/pull/3210) (cf. [this comment](https://github.com/coq/ceps/pull/48#issuecomment-727020253) by **@ejgallego**); otherwise (without native support), Dune will just ignore the native parts and no `./coq-native/*.cmxs` file will be installed.

Note that these changes could be performed directly in the existing packages gathered in the [coq/opam-coq-archive](https://github.com/coq/opam-coq-archive) repository.

# Alternatives

* A different but related idea was mentioned in [Zulip](https://coq.zulipchat.com/#narrow/stream/237656-Coq-devs.20.26.20plugin.20devs/topic/Coq-as-compiler/near/216196895): "OPAM: try out coq as a compiler" ([PR coq/opam-coq-archive#595](https://github.com/coq/opam-coq-archive/issues/595)).
    * This would require opam 2.0 (which is not a drawback).
	* This could be viewed as an alternative of this CEP's package flag.
	* Unfortunately, this alternative would be even coarser than this CEP (as all opam packages, not only those of coq libraries, would be recompiled).

* A new strategy, called `split-native`, has been discussed in the [CEP PR](https://github.com/coq/ceps/pull/48):
    * Assume a coq package `foo2` depends on `foo1`; there would be two extra packages `foo2-native` and `foo1-native`, with at least the following dependencies:
	    * `foo2` → `foo1`
		* `foo2-native` → `foo1-native`
		* `foo2-native` → `foo2`
		* `foo1-native` → `foo1`
    * This idea relies on the ability to generate `./coq-native/*.cmxs` directly from the `.vo` files.
	* A PoC of this idea has been implemented in [PR coq/coq#13287](https://github.com/coq/coq/pull/13287).
	* Yet this PR won't be ready for Coq 8.13, and it will also require some extra tooling, to automatically generate the `*-native` packages, and more generally keep `coq/opam-coq-archive` maintenance tractable.
	* And there might be some corner cases where, e.g., package `foo` contains both `A.v` and `B.v`, `B` requires `A` and relies on `native_compute`.
	* Finally, the implementation of the `coqc -native-compiler ondemand` setting could be optimized.

# Conclusion and perspectives

* This CEP was discussed at the 2020-11-13 weekly Coq call, in order to provide full-blown `native_compute` support for the Coq 8.13 release (cf. [PR coq/coq#13352](https://github.com/coq/coq/pull/13352)).
* The Coq team agreed on considering this CEP for Coq 8.13, while the `split-native` strategy could be further developed for a later Coq release.

*Note:* at the time this CEP is written, the Coq refman still lacks some documentation of the `-native-compiler` option; but progress on this is tracked in issue [coq/coq#12564](https://github.com/coq/coq/issues/12564); and that doc might incorporate [the array above](#regarding-item-2).

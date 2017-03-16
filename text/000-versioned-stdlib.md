- Title: A versioned, independent, development model for the standard library

- Drivers: @Zimmi48 (co-drivers could be @ejgallego @herbelin @mattam82 @amahboubi ...)

- Status: very preliminary draft, RFC

----

# Summary

Versioning the standard library independently from Coq itself
is important for better compatibility, especially in a development
model where new versions of Coq are quite frequent.

For practical reasons, this is better done by moving the `theories/`
files out of the main repository and into a specific coq/lib repository.

This move will also be a perfect opportunity to make sure that users
are encouraged to contribute to the improvement of the library,
and possibly to find additional maintainers coming from the user community.

# Motivation

The main motivation is to address the compatibility concern expressed
by lots of users, at the level of the library. Moving to an independent
versioning scheme will allow users to upgrade Coq without changing their
version of the library; and to upgrade their dependency on the library
without changing their version of Coq.

# Detailed design

A new repository coq/lib is created which contains the current state of
the `theories/` files.

The development of the library continues in this repository and follows
semantic versioning.

## Semantic versioning means:

- major versions can introduce breaking changes: they can add and remove
things, change definitions, change names of theorems;

- minor versions are about non-breaking improvements: they can only add
new definitions and theorems; adding a new theorem to a hint database is
considered a minor change: if users' scripts are relying on the failure
of an automatic tactic (except if this tactic implements a specific
decision procedure), it is completely fragile and thus it is their problem;

- patch level versions are about fixing bugs: bugs are deviations between
specification and implementation in definitions and decision procedures;
normally if enough theorems are proved about a definition, it will
probably not be buggy and thus patch level versions should be quite rare.

## Development practices

There is one branch per released major version (the stable branches, which
are named v1, v2, v3...) plus the master branch.

Breaking changes are always done on the master branch only.

Non-breaking changes are always done on the latest stable branch, then
merged into the master branch.

All the supported versions of the library (the development version, the
stable version and possibly a few legacy versions, i.e. older stable
versions) are checked to compile with all the supported versions of Coq
(thanks to automatic testing jobs).

## Distribution

The latest stable version and possibly some legacy versions are directly
included in the Coq packages which are distributed for Windows, MacOS and
Linux distributions.

All the other versions, including the development version, are accessible
through OPAM packages, or by manually downloading and compiling the
corresponding archives.

## Call for contributors

Once the split is done, it would be a good thing for the library to have
its own webpage and motivated maintainers who spread the word that it is
open to contributions from the Coq user community.

It can be discussed later but maybe some library developers would like to
integrate part of their work directly in the standard library.

The models here could be the QED project and the archive of formal proofs
of Isabelle (and contribution models of other provers, e.g. Mizar, ACL2...).

# Drawbacks

The main drawback is that the split makes it harder to continue compiling
Coq and its library. We discuss the proposed solution here.

We make git ignore the `theories/` directory. This folder will continue
to serve the purpose of developing and building the library.

Calling a special make target would look for a git repository at `theories/dev/`.
If it exists, it would fetch and checkout the latest changes from the master
branch at coq/lib, otherwise it would just clone coq/lib at this location.

Then it would look for git worktrees at `theories/v*` for each supported
version. It would create missing worktrees and would fetch and checkout
the latest changes from the corresponding branches at coq/lib for existing
ones.

Then it would build all the libraries under `theories/`, including those
it didn't cloned / checked out but which just happen to be there.

The recommended way of developing the library would be to create a new
worktree for each new branch you want to test in parallel. In particular,
the automatically created worktrees shouldn't be used because they are
there to track the current state of the library. In case this is not
respected by the developer, we would have to make sure that the make error
is crystal clear.

# Alternatives

## Alternative solutions to the compilation issue

An alternative to be able to compile the library from the main repository would
be to use git submodules. I strongly reject this option because, to me, git
submodules are useful to pull external dependencies which you don't update
often, not to keep two developments by the same team in sync (otherwise
submodule updates are too frequent).

## Alternative solutions to solve the compatibility issue

The main alternative is the status quo, and being really careful not to
break compatibility when doing changes, and to introduce compatibility
aliases when they are needed.

# Unresolved questions

- How many versions to support? This will have to be decided depending on
the user demand, and also on the capabilities of the maintainers. In
particular, the forthcoming consortium could help in maintaining a larger
number of legacy versions.

- Splitting the library in several parts has been discussed quite a few
times in the past. To me this question should be postponed until the new
development model is well tested. Then this question can be asked again
with more confidence (if it still seems to be relevant).

- Some plugins (omega, nsatz...) depend on the library. There are two
solutions here: either move them to the new repository, or keep them
where they are for now and make the efforts so that plugins continue
to be compatible with the various versions of the library.
The second solution has the advantage to reduce the amount of changes
required by the move, but it can turn out to be more complicated to
manage in the long run.
Keeping them where they are at the beginning does not prevent to move
them later though.

# Perspectives

If this new development model and versioning scheme is successful, it
could then be adapted to some plugins such as Ltac, but also CoqIDE,
the IDE protocols, and even the unification algorithm. But going too fast
would be risky and the standard library is a relatively simple example to
start with.

- Title: Coq and Coq platform release cycle

- Driver: Enrico

----

# Summary

We aim at a release process for Coq and the Coq platform which makes it
easier for users to provide feedback and for developers to deliver fixes.

In a nutshell the Coq "beta period" is replaced by a Coq platform "beta period".
Coq devs tag an almost final version on top of which the Coq platform core is
built. Coq point release are then used to *quickly* deliver fixes
to the platform.

# Motivation

The beta testing period does not provide enough feedback to sensibly improve
Coq between the `VX+beta1` and `VX.0` tags. The reasons are, most important
last:
- users have better things to do, frankly
- one month is short, especially with Christmas, summer holydays or conferences
  around (our beta period is December or May)
- in order to test Coq you are likely to need a bunch of Coq packages, and they
  are typically only available after the beta period is over

Moreover the "beta period" is also seen by devs as a time frame where they can
still change many things. As a results users are even less happy to spend time
working on a moving target.

Finally, due to the cost of backporting breaking changes from the master
branch to the release branch, this only happenes very early in the release
cycle (for example only 2 such changes were backported in the beta period
for 8.12, 0 for 8.13).

## New actor: platform

The Coq platform is a selection of Coq packages which work well
for a given Coq version. One of its objective is to disentangle the release
of Coq with the release of other packages. It provides scripts that build
that selection of Coq packages on Windows, Mac and Linux from sources
on the user's machine, and as well binary installers (prebuilt) for users
to quickly get a working environment.

This product is what users will test in this new model; Coq is a core
component of it.

# Detailed design

The new process' timeline:
```
                     D             D            D   D  D
coq      --+---(1)---+------(2)----+-----(3)----+---+--+----
 vX branch/          |             |            |
            X+rc tag/              |            |
                           X.0 tag/             |
                                        X.1 tag/

                                   I                    I
platform  -----------+----(4)------+--------(5)---------+
           vX branch/              |                    |
                        X+beta tag/                     |
                                                X.0 tag/
Artifacts:
- D = docker image for Coq (and opam package)
- I = binary installers for Coq platform (and opam packages and docker image)
```

## Coq

On time based schedule the RM branches vX.

1. The RM shepherds the few PR which are ready and pins projects tracked by CI
   (using commit hashes, not necessarily tags). Then he tags Coq. This should
   take 10 days. No packages are built, just a git tag. A docker image is built,
   so that project maintainers can use it in CI. No breaking change is allowed
   from now on (unless a severe problem is found).
2. Doc is updated (eg. Changes file) and eventual fixes required by the platform
   are done. Ideally no other change is done. This should take 10 days.
3. In response to a severe bug report Coq devs make an hotfix in master which is
   backported to vX by the RM which then tags a point release, possibly as soon
   as the fix is available and merged.

## Platform

When Coq X+rc is tagged, the PRM branches vX

4. Starting with the pins made by RM on Coq's CI all packages part of the
   platform (or its core) are pinned (in accordance with upstreams, which are
   notified about the ongoing process). Most, if not all, packages are in Coq's
   CI so there should be no surprises, otherwise issues are reported to Coq
   devs. When done a X+beta tag is done and packages made available to users.
   A docker image with the entire platform prebuilt should be built. This
   should take 20 days.
5. As users pick up the platform and find severe bugs in Coq, the platform picks
   up point releases of Coq containing hotfixes and eventually extends packages
   beyond the core set.

## Synchronization points

- The end of (1) starts the release cycle of the platform.
- The end of (2) and (4) don't need to be done at the same time, but if they
  are then the new release cycle coincides with the old one (up to the
  renaming of X.0 into X+beta).
- Coq's X.0 tag can be made as soon as the doc is clear. This will stress the
  fact that upstreams can pin with no worries.

## Announces

- Coq tags are only announced to devs
- Coq platform pins are communicated to upstream devs, which may tag/release.
- Coq platform tags and packages are announced to the community

## Coq CI

- must test standard configurations
- must test all platform projects with ML parts
- must test a selection of platform scripts (to test the script themselves,
  not the build of platform packages)
- should test platform projects with V files which are depended upon in the
  platform
- can test anything else of course, including non standard configurations

## Platform CI

- on branch vX it should test all packages and build installers as artifacts
- on branch master it should take Coq master and its pins for the subset of
  packages it covers and test all the packages, eventually report the
  failures upstream

### Terminology
- "severe bug" is a bug which *blocks* many users with no decent workaround,
  or a soundness bug.
- "hotfix" is a minimal patch that repairs a problem, not necessarily the nice
  solution which may require refactoring or cleanups. The patch should pass CI
  with no overlay and must be reviewable (in a strict sense, as in looking for
  bugs, not just as in "looks reasonable")
- "RM" is the release manager of Coq
- "PRM" are the release managers of the Coq platform
- "standard configuration" is a version of ocaml and other tools which are
  agreed between Coq devs and the platform devs (dune, make, gmp, gtk...)

# Drawbacks

This new process identifies 3 groups of developers which need to talk to each
others: Coq dev, platform devs, and docker devs. This is a risk, but also an
advantage since the Coq release becomes more lightweight, leaving the RM
more time to focus on supporting the release with hotfixes.

# Alternatives

We consider docker as *the* platform upstream projects use for testing.
This may be a bit narrow, even if the docker stuff on coq-community is
pretty good IMO.

# Unresolved questions


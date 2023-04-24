---
Title: Future of CoqIDE
Drivers: Karl Palmskog (@palmskog), Théo Zimmermann (@Zimmi48)
---

## Summary

The goal of this CEP is:

1. to clarify the priority and focus shift by the Coq team away from maintaining and evolving CoqIDE;
2. to give an opportunity to the community of CoqIDE users to assume maintenance  of and lead the future evolution of CoqIDE through a source code split out of the Coq GitHub repository.

More specifically, the proposal is to make an open call for new volunteer maintainers of CoqIDE through Coq community channels, and then to proceed with a source code split only if volunteer maintainers are found.

## Context and motivation

[CoqIDE](https://coq.inria.fr/refman/practical-tools/coqide.html) is an Integrated Development Environment (IDE) for Coq. CoqIDE is implemented using the OCaml programming language and the GTK3 widget toolkit for Graphical User Interfaces (GUIs), thanks to the [lablgtk3](https://opam.ocaml.org/packages/lablgtk3/) OCaml package.

CoqIDE communicates with Coq thanks to an [XML protocol](https://github.com/coq/coq/blob/master/dev/doc/xml-protocol.md), implemented by the coqidetop server (in the coqide-server opam package), which itself is based on a component in Coq called the [State Transaction Machine](https://coq.github.io/doc/master/api/coq-core/Stm/index.html) (STM).

The drawbacks of CoqIDE and coqidetop are that:

- maintaining a standalone IDE just for Coq means that a lot of standard work has to be redone and lots of standard IDE features are not implemented,
- the XML protocol is entirely custom and suited for the CoqIDE implementation, which means that any IDE wanting to interface with Coq through this protocol has to reimplement a lot of things, and that it won't always be well-suited to the model that the IDE expects.

Recently, the Coq team has changed its strategy, by focusing instead on developing support for the [Language Server Protocol](https://microsoft.github.io/language-server-protocol/) (LSP) with minimal extensions, which should bring the possibility to develop Coq support for any standard IDE (starting with VS Code). Meanwhile, CoqIDE, coqidetop and the STM are considered outdated technology that the Coq team would like to avoid putting too much work into maintaining.

Because *some users still prefer a standalone IDE for Coq*, and some are *motivated to contribute to CoqIDE*, we want to give the opportunity to the community to take over CoqIDE maintenance by splitting out the CoqIDE source code from Coq's repository, on the condition that volunteer maintainers are found.

## Detailed design

### Short-term actions

Upon acceptance of this CEP, we will send an open call for volunteer maintainers. The planned text of the call is available below, in an appendix to the CEP's main text.

In the case where volunteer maintainer(s) are found:

1. The code for CoqIDE (the UI part) will be split into a separate repository (the code for coqidetop and the STM will remain in the Coq repository for as long as there are other major users besides CoqIDE that depend on them). The repository will temporarily be created in the Coq organization.
2. Any issue in the Coq issue tracker pertaining to CoqIDE will be moved to this new repository.
3. The repository will be transferred to the [Coq-community organization](https://github.com/coq-community/manifesto).
4. The volunteer maintainer(s) will be given admin access to the repository.
5. CoqIDE will be added in Coq's Continuous Integration (CI), but there is no commitment from the Coq team that it will get to stay there indefinitely.
6. CoqIDE will keep being distributed as part of the [Coq Platform](https://github.com/coq/platform), for as long as it respects the inclusion criteria (timely release of compatible CoqIDE versions with new Coq releases), but will no longer be considered an official project by the Coq team.

The new CoqIDE maintainers will receive support from both the Coq team (for as long as CoqIDE is in Coq's CI, more about this in the next subsection) and from the Coq-community organization owners (to set up solutions for CI, deploying documentation, protecting branches, etc.), but they will have complete freedom to define:

- what features / changes to include,
- what technology / internal changes to make,
- which versions of Coq to support,
- how to review and merge changes (in particular, we expect that the reviewing process will become more lightweight than it is currently in the Coq repository, with the ability, in particular, to self-merge some pull requests),
- when and how frequently to release new CoqIDE versions (keeping in mind that some releases will be mandated by the Coq Platform inclusion).

A recommendation to CoqIDE maintainers is to quickly make CoqIDE compatible with multiple Coq versions (at least when the XML protocol doesn't change). This technically already works with the limitation that CoqIDE doesn't check for the version of Coq: https://github.com/coq/coq/issues/16521.

### Long-term plans

As explained above, members of the Coq team are currently developing support for LSP, along with VS Code extensions. There are two projects in this direction: 
- [VsCoq2](https://github.com/coq-community/vscoq), a project for a stable Coq IDE led by Inria engineers and supported by stable Inria funding, and 
- [coq-lsp](https://github.com/ejgallego/coq-lsp), a research project led by an Inria researcher and supported by research grants. 

The two projects are based on different architectural choices and allow exploring different directions, but in both cases, they work with no dependency on the STM (VsCoq2 is based on a [new document manager](https://github.com/Coq-community/vscoq/blob/main/docs/developers.md#architecture) that can be considered as an evolved, more modular, and smaller STM, while coq-lsp is based on an incremental document checking engine called Flèche). There are hopes that despite the different architecture and implementation, the specification of the LSP extension that they implement can eventually be shared. coq-lsp is already available for use with recent versions of Coq, and VsCoq2 is planned to become available with Coq 8.18.

When Coq LSP support becomes stable enough, maintainers of IDE support packages for Coq (e.g., Proof General for Emacs, Coqtail for Vim) will be encouraged to migrate to using this protocol. We expect that Coqtail will be one of the first IDEs to migrate, as it currently depends on coqidetop and the XML protocol (and such a migration has already [seen experiments](https://github.com/whonore/Coqtail/pull/323)).

When no major IDE besides CoqIDE relies on the XML protocol anymore, the Coq team will start considering removal of coqidetop from the Coq repository. It will then become time for CoqIDE maintainers to decide what to do regarding the long-term future of CoqIDE. At this point, several options will be available:

- declare the end of the CoqIDE maintenance,
- migrate CoqIDE to rely on LSP instead of the XML protocol, following the example of other IDEs, but without the support of standard parts of LSP being natively suported in the editor,
- keep maintaining coqidetop for as long as the required APIs / components are there in Coq. 

Note that coqidetop depends on the STM, and that the STM will be eventually removed from Coq (or features from the STM will be gradually removed) as STM users are gradually migrated off it or deprecated. (Besides coqidetop, another major STM user is [SerAPI](https://github.com/ejgallego/coq-serapi), on which [Alectryon](https://github.com/cpitclaudel/alectryon) is built, but there are already plans to migrate Alectryon off SerAPI and deprecating SerAPI in favor of coq-lsp.) At this point, if CoqIDE requires specific APIs that the Coq developers do not want to maintain, they won't hesitate to remove CoqIDE from Coq's CI.

Other factors are likely to affect the future of CoqIDE, in particular its dependance on GTK3 through lablgtk. Migration from GTK2 to GTK3 was only possible thanks to a coordinated effort by maintainers of multiple GUIs to contribute to update lablgtk for compatibility with GTK3. We don't know if similar efforts will happen to make lablgtk keep up with changes to GTK (which is currently already at version 4). The number of GUIs depending on [lablgtk3](https://opam.ocaml.org/packages/lablgtk3/) is already much lower than the number that used to depend on [lablgtk2](https://opam.ocaml.org/packages/lablgtk/). It is possible that Frama-C or Why3 decide to similarly prioritize VS Code support and stop contributing to the lablgtk ecosystem.

## Drawbacks

- By giving the opportunity to the community to take over the maintenance of CoqIDE, we create the possibility that maintenance effort will be put in a technology that ends up outdated and unmaintained after a few years anyway. This is why this CEP tries to highlight not only the short-term benefits, but also the long-term risks.
- Another risk is that because new CoqIDE maintainers may have less strict reviewing and releasing policies, new CoqIDE versions include regressions affecting its user base (which is still quite large). In this case, we hope that the added flexibility in the CoqIDE maintenance will allow producing new releases which fix these regressions quickly, or that compatibility with several Coq versions will allow maintaining several lines of CoqIDE in parallel (e.g., a more stable line and a more experimental one with new features).

## Alternatives

- The main alternative is to keep CoqIDE as part of the main Coq repository and as an official Coq project. In this case, the Coq team is not ready to do more than the minimal amount of maintenance effort because of its shift in priority focus. Therefore, users shouldn't expect big improvements to CoqIDE, even if they come from pull requests by external contributors (there will be no guarantee that these get reviewed and merged, as CoqIDE will be considered mostly "frozen").

## Unresolved questions

- Previous calls for volunteer maintainers (VsCoq1, Docker-Coq) have included a mention that the maintainers would be given recognition by adding them on the official Coq Team page. In this case, since the goal is to remove the official status of CoqIDE, it is not clear that this would be appropriate. If CoqIDE maintainers are acknowledged on this page, perhaps we should extend it to also acknowledge maintainers of other Coq IDEs, such as Proof General, Coqtail, and jsCoq.

## Appendix: Call for volunteer maintainers of CoqIDE

The Coq core team and Coq-community are looking for volunteer maintainers of the CoqIDE project.

CoqIDE is an Integrated Development Environment (IDE) for Coq. CoqIDE is implemented using the OCaml programming language and the GTK3 widget toolkit for graphical user interfaces (GUIs). CoqIDE uses a legacy XML-based protocol to communicate with Coq and is licensed under the open source LGPL-2.1 license.

CoqIDE's source code is currently part of Coq's GitHub repository. Due to a desire to shift IDE-related work toward LSP and VS Code support, the Coq core team no longer considers CoqIDE maintenance and evolution a priority. With this call, the team wants to give an opportunity to the Coq community to take over CoqIDE maintenance and lead its future evolution.

If maintainers are found, CoqIDE sources will be moved to a repository in the Coq-community organization on GitHub, where it will receive support and fixes from the core team for a limited time. If no maintainers are found, CoqIDE sources will be kept in Coq's repository and minimally maintained until their eventual removal.

More details about the context and the plans for the future of IDEs for Coq can be found in the CEP leading to this call: \<add link to this CEP here\>

Please respond to this GitHub issue with a brief motivation and summary of relevant experience for becoming a CoqIDE maintainer. The maintainer(s) will be selected from the issue responders by the Coq core team and Coq-community organization owners. Responders not selected will still be encouraged to contribute to CoqIDE in collaboration with the new maintainer(s) and other contributors.

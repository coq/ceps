- Title: A Compilation of Short Interactive Tutorials and How-To Guides for Coq
- Drivers:
    - Thomas Lamiaux / @thomas-lamiaux / thomas.lamiaux@ens-paris-saclay.fr
    - Theo Zimmermann / @Zimmi48 / theo.zimmermann@telecom-paris.fr
    - Pierre Rousselin / @Villetaneuse / rousselin@math.univ-paris13.fr

----
## Table of Content

1. Summary
2. Motivation
   2.1 The lack of action-oriented documentation
   2.2 Why it is important
3. A compilation of interactive tutorials and how-to guides
   3.1 General Design
   3.2 A Horizontal Documentation
   3.3 Online interface
4. Organisation
   4.1 First Steps
   4.2 Writing the documentation
   4.3 Maintenance and evolution
   4.4 Web Interface
   4.5 Moving on to the official Coq repository and Coq's webpage
   4.6 Human resources


---
## 1. Summary

The goal of this CEP is to discuss the design of an online compilation of short and interactive tutorials and how-to guides for Coq and the Coq Platform.

Each core functionality and plugin of Coq and the Coq Platform should have (short) pedagogical tutorials and/or how-to guides demonstrating how to use the functionality, with practical examples. Tutorials and how-to guides serve different purposes and are complementary: tutorials guide a user to discover a specific feature like "Notations in Coq", by going through predetermined examples, and introducing notions gradually, whereas how-to guides are use-case-oriented and use examples to show what to do in front of a specific problem (and possibly the various alternatives to address it). See https://diataxis.fr/ for a reference definition of tutorial vs how-to guide (in particular, https://diataxis.fr/tutorials-how-to/ for a comparison).

Compared to the reference manual, such a documentation is not meant to be complete or going into low level details. It is meant to be pedagogical and action-oriented, so that it enables users to learn how to use new features autonomously and horizontally : these tutorials and how-to guides should be as self-contained as possible to have only a short (if any) list of prerequisites. Moreover, by being horizontal, such a documentation could provide different tutorials (for some specific features) to cover the needs of users with different backgrounds.

---
## 2. Motivation

Having a proper, clean and accessible documentation is one of the keys to the success of software. There are different forms of documentation: abstract and detailed documentation like the reference manual, course-shaped documentation like Coq'Art or Software Foundations, or short action-oriented documentation. In this CEP, we focus on the latter.


### 2.1 The lack of action-oriented documentation
Short action-oriented documentation provides users with practical information on specific features of Coq, so that they can both learn and discover new features by themselves, but also consult them when they are trying to use these features and are stuck.

Apart from long, course-shaped books, Coq currently has only minimal and scattered action-oriented documentation.
The reference manual is by design not learning-oriented and not action-oriented, and it would be a mistake to try to bend it that way: it is not its purpose. It also provides relatively few examples (although many new examples have been added in the past few years and more would be welcome) and it is focused on Coq core features.
Books like Coq'Art or Software Foundations provide nice pedagogical explanations but target specific audiences, and are often meant to be read from cover to cover. Moreover, they are not well suited to learn about specific features, to discover horizontally, and are not easy to keep updated.
Other great resources exist like [Coq Tricks](https://github.com/tchajed/coq-tricks) or package-specific tutorials, but they are limited and are not necessarily easy to access for newcomers.


### 2.2 Why it is important
Not having a central collection of short and action-oriented documentation pieces is a real obstacle to getting more users outside of expert academic fields, and for Coq's popularity.

#### Accessibility
Having an easy to access documentation is of utmost importance to engage new users, and keep current users. Although it does work for some experts, we cannot expect from all potential new users to have to dig through a (possibly outdated) 600 pages book, or the reference manual to learn how to use a particular feature that appeals to them. Most particularly as these sources may not contain the basic answers they are looking for due to their nature. Similarly, having to say "try to look in the GitHub repository of the package, there might be some documentation there" is not possible if we wish for our software to be usable by all. Practical and pedagogical information must be easily accessible through a **nice** centralized online interface. This is especially true, at a time when new proof assistants emerge and attract new users outside computer science research.

#### A documentation focused on practical usages
Furthermore, not having such a documentation prevents people from actually learning by themselves, and discovering new amazing features of Coq that rival proof assistants may not have, as well as the richness of our ecosystem. While a lot of progress has been made on the ecosystem side with pages like [Awesome Coq](https://github.com/coq-community/awesome-coq) and the Coq Platform, there is still work to be done for the documentation that is hard to access. Many amazing features are still currently under-documented, and the existing documentation is often scattered out in the reference manual, books, or individual GitHub repositories, making it difficult to access. A symptom of that is the trouble that students are currently facing to discover new functionalities by themselves, compared to other software. In particular, in our experience, it is quite common that users (have to) rely on expert users they know to learn Coq.

Even for fluent Coq users, it can be challenging to keep up to date with the many recent interesting developments inside Coq (template polymorphism, universe polymorphism, SProp, Ltac2, ...) or around Coq (coq-elpi, metacoq, hierarchy builder, ...)

Also, many users are currently unaware of the extent of what has been formalized and is available in Coq. There are many libraries, and it is not easy to know which library to use, or to know on which axioms they rely or their compatibilities.
This is obviously not just a documentation issue, but having a clear documentation of what we have and where would help.

#### Finding bugs or undesirable behaviours from the non-expert user's point of view
From a different perspective, writing documentation forces us to study in depth some features (possibly with the help of expert developers), and consequently to understand better these features, and their basic applications. We hope that by writing the documentation, we will clarify the use of many features, and potentially discover bugs. Actually, writing tutorials [for Equations](https://github.com/Zimmi48/platform-docs/pull/1#issuecomment-2098810034) has already revealed different issues including unwanted behaviour from one of the main features.


---
## 3. A compilation of interactive tutorials and how-to guides

To address this issue, this CEP suggests building a centralized online compilation of short and interactive tutorials and how-to guides for Coq and the Coq Platform.


### 3.1 General Design

#### Tutorials

##### What tutorials should be
Tutorials are meant to introduce and explain the different aspects of a functionality step by step with examples. As Coq is, at its core, an interactive system, tutorials should be interactive as well. We want to provide action-oriented documentation that users can run to discover how to use a specific feature, and a (non-exhaustive and opinionated) material that they can come back to, as a practical reference.
For instance, we could write tutorials about "tactics for forward reasoning", "notations in Coq", "the Equation package", etc...

Tutorials do not necessarily need to be long, nor should aim to present all the aspects of a feature in one unique tutorial, as they do not have the purpose to be exhaustive like a reference manual. On the contrary, the various independent aspects of a feature should be split into several tutorials. Moreover, tutorials can also be split in order to provide a more gradual introduction to a complicated feature.


Doing so has the advantage to make it easier to navigate for users that can look up specific content without having to go through independent ones.
It also has the advantage to make it easier to write and to update, as we can start by writing a tutorial on the basics of a feature, and then gradually enrich the documentation with more specific / advanced tutorials over time.

When possible, tutorials should try to be as self-contained as possible, and should not hesitate to recall quickly a concept rather than referring to another tutorial. Doing so only takes a bit more time when writing a tutorial but saves a lot of time to users that will not have to chase information in different other tutorials, tutorials which could in turn refer to other tutorials.
It also eases maintenance as one does not need to worry about potential modifications to other tutorials.

Otherwise, note that tutorials are not meant to discuss in detail how a feature works internally, as this is the job of [another kind of documentation](https://diataxis.fr/explanation/) (called "explanation" or "discussion" in the Diataxis framework), that could be added later.

Similarly, there is no need to have a tutorial for every single functionality of Coq. Typically, there is no need to write a tutorial for deprecated features.

##### Encouraging developers to write tutorials

While designing tutorials from scratch can take some time, most projects already come with research papers containing examples and demos which can be reused.

Moreover, a tutorial about the basics of an automation tactic does not necessarily need to do more than:
1. showing how to set up and use the tactic
2. demonstrating through examples what kind of goals it can solve (or not)
3. potentially showing some options that the tactic can take to solve more goals

We think that most tutorials will be stable over time, so they will not require too much maintenance time for developers. Moreover, since we want tutorials to be short and independent, they need not be written in one go.

We want to encourage developers to provide tutorials along with the software component they maintain, or to work closely with a tutorial author to create this tutorial. We are convinced it will be fruitful in terms of number of users and relevance to user needs.

##### Examples
As an example, with its developers, we have been working on new tutorials for the package Equations using the examples available on the associated repository.
We have already written drafts for three tutorials:
- A tutorial `Equations_basics.v` that discusses the basics of defining functions and reasoning with Equations.
- A tutorial `Equations_wf.v` that explains how to reason by well-founded recursion using Equations.
- A tutorial `Equations_indexed.v` discussing the particularities of reasoning on indexed inductive types.

Both tutorials `Equations_wf.v` and `Equations_indexed.v` rely on the tutorial `Equations_basics.v`, and are independent of each other. This enables the users to only have to read the basics to be able to start working, and leaves them the possibility to learn new aspects of Equations in a modular fashion, according to their needs. Moreover, having mostly independent tutorial enables us to easily add new tutorials over time, e.g. we could add a tutorial on proof carrying code without changing the other tutorials.


#### How-to guides

How-to guides are meant to guide users step by step through a real life problem, from its different aspects to its resolution.

Therefore, they should not be about touring a particular feature like "How to use notations", this is the point of tutorials. They should not be too general either like "How to use Coq". They should start from the practical needs of users and lead progressively to a practical solution. For instance, "How to use type classes to automate proofs" or "How to use hierarchy builder to structure a library".

In this regard, how-to guides are meant to be practical to use, and should only contain the information necessary to understand and solve the problem. Yet, this does not mean they should be simplistic. At the opposite, as they are meant to answer real life issues, within reason, they should try to account for real life complexity. The structure of how-to guides should not be afraid to reflect that, in particular to be non linear in the limit of what is reasonable. Typically, a section could start by distinguishing the different most common possibilities, and have a subsection per possibility.

Tutorials and how-to guides are different by nature yet complementary, and a feature can have both or just one of those. Tutorials are meant for studying and acquiring new skills, whereas how-to guides are about applying them in practice on real life examples. In particular, tutorials follow direct and controlled paths on simplified examples whereas how-to guides must account for the complexity of real life.



#### Introductory Games

Tutorial and how-to guides are meant to explain through examples specific features of Coq and its platform, but not to introduce Coq, or to be a course on Coq to follow in a specific order.

Yet, in our preliminary discussions, we have seen a need for this kind of content to ease the first steps in the ecosystem, in particular for introductory games like the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) or the [Hott Game](https://homotopytypetheory.org/2021/12/01/the-hott-game/), that provide a nice introduction to Coq or to a concept and its very basic aspects in a fun and engaging way.

Designing games is very different than designing tutorials or how-to guides, and will require a specific work on the subject.
In particular, there may be more than one introductory game, depending on what is meant to be introduced, Coq and logic, HoTT, programming in Coq, and potentially on the background of the users.


### 3.2 Horizontal Documentation
Such a documentation has by nature the potential to be horizontal as most pairs of tutorials have no reason to be linked. Ensuring it by design is very important for the documentation to be accessible, and will allow by nature differentiated learning.

#### Accessibility

As we have already said, an effort should be made so that tutorials are as self-contained even if it means adding some reminders. Moreover, it is important that users do not have to know, e.g., how `lia` works to get to know how sections work and conversely. Similarly, it is important to be able to sandbox Coq's theory as much as possible. While it needs to be discussed as well, we do not wish for users to have to learn Coq's type theory to learn how to use sections or other such mechanisms. As reported by some Coq users we discussed with, when one asks something simple about Coq, many things can come all at once.

#### Writing and Maintaining

Contrarily to a very linear and structured course about Coq, horizontal tutorials and how-to guides make it easier for many authors to write in parallel documentation about very different aspects, and to add content progressively.

#### Differentiated learning

Being horizontal, such a documentation would enable to have different tutorials (for some specific features) for different users. For instance, one could have:

- Different tutorials depending on the background, e.g. for mathematicians or engineers.
- An Ltac2 tutorial for people that already know Ltac, and a tutorial for newcomers.
- Different tutorials depending on the level of the user, e.g. a basic tutorial about inductive types, and a more advanced one discussing notions like strict positivity or the guard condition.

It would also have the advantage to be (relatively) easy to maintain as the tutorials would mostly be independent, short, and in a reasonable number.


### 3.3 Online interface

The documentation would be interactive and available online, in a format more or less similar to [Pierre Rousselin's class](https://www.math.univ-paris13.fr/~rousselin/ipf/2023/RInegalit%C3%A9s_sujet.html).

Having an interactive interface is essential for accessibility as it does not require users to have to install and set up Coq and different packages just to try a feature.
While it is now much easier with the Coq platform, it can still be challenging for newcomers and non computer scientist, and it remains particularly interesting for introductory tutorials and teaching.
Moreover, it enables to easily switch between tutorials without having to constantly download a bunch of Coq file, while still enabling those who wish it to do so.

At this point, from a unique text file, we wish to generate three versions of each tutorial:
1. a `.v` file which should still be downloadable and readable with any text editor,
2. a non-interactive web page with embedded Coq output to be used, e.g. with a smartphone,
3. an interactive web page embedding Coq.

The interactive and non-interactive web page could be just one `html` file where interaction is triggered by a button. The `.v` file could also be downloaded from the same page via another button.

The `html` would be generated from the `.v` file via a tool like [Alectryon](https://github.com/cpitclaudel/alectryon), which provides a means to interpret restructured text in comments inside Coq files (and conversely Coq code blocks inside restructured text files), and to produce an `html` output. This provides us with a simple but versatile and standard format, compared to other tools like coqdoc (which uses its own and more limited markup language).

To account for the different versions of Coq and of the plugins, the documentation would be indexed on the releases of the Coq Platform similarly to how the reference manual is for Coq.

We wish this documentation effort to be part of the next version of Coq's website similarly to what can be found on [the OCaml website](https://ocaml.org/docs/lists).

---
## 4. Organization

### 4.1 First steps

To start the project, we have created a repository on GitHub on which users can already contribute, and a [dedicated channel on Zulip](https://coq.zulipchat.com/#narrow/stream/437203-Platform-docs).

We have already worked on a few tutorials as examples, which can be found on [Théo Zimmermann's repository](https://github.com/Zimmi48/platform-docs). These tutorials are already useful for Coq users and have exposed some undesirable features, bugs or omissions both in the features themselves and their current documentation: see, e.g. this pull request about [Search](https://github.com/coq/coq/pull/18983) and this one about [Equations](https://github.com/mattam82/Coq-Equations/pull/604). We received a lot of reviews from experts.

At the moment, as a proof of concept, we use coqdoc to format our documents and the current version of [jsCoq](https://github.com/jscoq/jscoq). The (very preliminary) output can be seen [here](https://www.theozimmermann.net/platform-docs/).
As mentioned in section 3.3, we aim in the future to use a more versatile and standard format for `html` document generation.

### 4.2 Writing the documentation
Writing the different (pedagogical) tutorials will be challenging considering the amount of the work there is to do. Thankfully, many functionalities or plugins of Coq already have documentation in a form or in another.
Part of this work will involve gathering them, as well as sometimes updating them, or making them more accessible.
Other tutorials will have to be written from scratch. We will organise directed calls for contributions to avoid having multiple overlapping / rival tutorials.
Among other possibilities, we will be in touch with plugins designers and expert users for the tutorials and how-to guides of their plugins.

As a base to work on, we suggest an [informal list](https://github.com/Zimmi48/platform-docs/blob/main/draft_structure_doc.md) of tutorials and how-to guides that we could have. This list has been established through informal discussions. It will necessarily evolve with the projects, contributions and user feedback. We further plan to go to CUDW and other similar events to discuss the project and the needs of the community.


### 4.3 Maintenance and evolution
The documentation is to be indexed on the Coq Platform releases so that a user can find documentation whatever its version of it, and to ease maintenance.

Once written, we expect the documentation to be relatively stable and easy to maintain as the tutorials and how-to guides should be relatively short, independent, and in limited numbers.

We identify three main reasons to modify an existing tutorial:
1. Some inaccuracies or omissions have been found by users, the text needs to be clarified, or missing parts need to be added.
2. We need the tutorial or how-to guide to follow the evolution of best practices.
3. We need the tutorial or how-to guide to evolve because of new functionalities, incompatibilities or API changes in a new version of the software component.

We plan to use three development branches in order to cope with these modifications:
- a stable branch, for the current version of the Coq Platform, where changes in the text would be necessary due to the first item above,
- a main branch, to prepare for the next Coq Platform release with changes mostly for the second and third reasons above,
- an edge branch, to be compatible with the development versions of Coq and its libraries and plugins.

We would like our edge branch to be part of Coq's CI, and to encourage plugins and library maintainers to integrate the (edge branch) tutorials about their component in their own CI. That way, they can detect incompatibilities in their new versions and correct the tutorials accordingly. These tutorials would also make good test files for their projects.

Furthermore, we expect Coq or Coq plugin and library developers to update tutorials (or at least find someone to do it) when they add a new feature to Coq or a new functionality to their plugins, just as they are supposed to update the reference manual.


### 4.4 Online Interface

We have identified 3 different components which play a role in making nice interactive web tutorials:
- First, we need a tool to format structured Coq comments (coqdoc, embedded `rst`, ...) into `html`. This tool and the associated format for comments should be easy to use to encourage more people to contribute.
- Second, we need a way to make Coq run inside a standard compliant web browser.
- Finally, we need a nice user interface inside the interactive web pages which will contain different views: the proof state, Coq's messages, possibly a Search view, ...

We already have some technical answers:
- [Alectryon](https://github.com/cpitclaudel/alectryon) provides means to interpret restructured text inside Coq files (and conversely).
- `jsCoq` and `waCoq` enable Coq to be executed inside a web browser, so there is a priori no insurmountable difficulty there.

Yet, it will require some real technical work:
- waCoq or jsCoq need to evolve to more recent versions of Coq and their usage with external libraries needs to be smoother,
- we have not tested yet how to use Alectryon and jsCoq/waCoq together.

Having such an easy to use online interface is of general interest for the Coq environment, e.g. teachers, so we hope they will be addressed soon.

### 4.5 Moving on to the official Coq repository and Coq's webpage
If this CEP is accepted, after discussion and amendments, we wish this documentation project to be part of the roadmap to gain visibility, and for the temporary repository to be moved to an official Coq organization repository.

While discussing with some developers, the idea also emerged for this documentation project to be integrated directly to Rocq's new website, similarly to what is done on [Ocaml's website](https://ocaml.org/docs/lists). This is also a question to address with this CEP.


### 4.6 Human resources

This project will necessarily have to be collaborative considering the amount of work to be done, and the richness and diversity of our ecosystem. No one has the time nor is competent to write or review expertly every single possible tutorial. Yet, as the tutorials can mostly be designed independently, by combining the different expertise of the different communities, there is good hope to quickly get to a good documentation, and we welcome contributions. We hope to attract more and more contributors and involve plugin writers and Coq developers in this process.

Yet, this project will require specific resources:
- As mentioned in section 4.3, there is real work to be done on the interface side.
- There is a need for someone interacting with the community, reviewing etc.

Thomas Lamiaux should be employed part-time on this project as a 3 years expertise mission included in his PhD. His task should be developing the project, writing and reviewing tutorials, and interacting with the community, ensuring at least some people-power in the beginning of this project.
However, in the long run, we may need to have someone (at least) part time specifically on this project, which seems, at least to us, important for the community.

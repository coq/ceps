- Title: CEP(es), Coq Enhancement Proposal

- Drivers: Enrico

----

# Summary

This document introduces CEP, documents describing the design of a feature
for Coq **before** implementing it.  Discussions on mailing lists or the bug
tracker hardly converge on a clear picture.  CEP are meant to produce clear
design documents that can be discussed at a working group, commented by Coq
users, implemented and finally used as a reference.

A CEP is a document like this one.  
Useful sections are
- title: a catchy title is key to success ;-)
- driver: your name/contact
- summary: from reading this part one should understand if he is interested and/or competent on the subject of the CEP
- motivation: it is important to explain which problem the CEP is trying to solve or which use case it covers
- detailed design: explain how the problem is solved by the CEP, provide a mock up, examples.
- drawbacks: is the proposed change affecting any other component of the system? how?
- alternatives: yes, do the related works
- unresolved questions: questions about the design that could not find an answer

## A CEP's life
During a rainy day you have a great idea? Make a CEP(e)! Write a simple draft,
a mock up of the syntax and an intuitive description of the semantics. Tell
your colleagues. Other insiders may get interested. Then work out more details,
and when the CEP is understandable make a pull request on the CEP repository.
Follow the discussion, comments, and update
the CEP.  When you feel things have settled,
bring it to the working group. The discussion at the working group may lead to
more iterations in the design process, or Accept the CEP or Reject it.

Then start implementing it, or find someone that does it.

## More concretely, what should a driver do
1. Fork the repo http://github.com/coq/ceps
1. Copy 000-template.md to text/000-my-feature.md (where 'my-feature' is descriptive. don't assign a number yet).
1. Fill in the CEP. Put care into the details!
1. Submit a pull request. As a pull request the CEP will receive design feedback from the larger community, and the driver should be prepared to revise it in response.  Discussion shall happen in the pull request "conversation" tab.
1. It is important to signal the CEP to the maintainers of the Coq subsystem to which it applies, see https://coq.inria.fr/cocorico/CoqDevelopment/Maintainers
1. When the design is ready, i.e. no known flaws are there, propose the merge of the CEP at the Next Coq Working Group https://coq.inria.fr/cocorico/CoqDevelopment/NextCoqWG
1. Acceptance is signalled by a merge of the CEP, rejection by closing the pull request
1. Eventually write code or find someone that does it

## FAQ
* *Why not a pull request (to https://github.com/coq/coq with the code)?* A CEP is about the design, and has to happen before code is written. A proof of concept (a toy implementation) is perfectly fine and may help the discussion. Still, pull requests on https://github.com/coq/coq are meant for code to be integrated, not for ideas to be discussed.
* *Why not a bug tracker entry? Why not a mailing list thread?* A CEP can be related to a bug number and discussion can happen on a mailing list.  A CEP summarizes the discussion into a more accessible document.  If you want to bring someone in the discussion a CEP is a single pointer to give to him.
* *What does `Accept` really mean?* Once a CEP is accepted then authors may implement it and submit the feature as a pull request to the Coq repository.  Being accepted is not a rubber stamp, and in particular still does not mean the feature will ultimately be merged; it does mean that in principle all the major stakeholders have agreed to the feature and are amenable to merging it.

## Changes
* 14/4/2016, first draft
* 24/1/2017, more details on the workflow
* 3/3/2017, take many ideas from the Rust RFC process

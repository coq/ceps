- Title: CEP(es), Coq Enhancement Proposal

- Drivers: Enrico

- Status: Draft

----

# Summary

This document introduces CEP, documents describing the design of a feature
for Coq **before** implementing it.  Discussions on mailing lists or the bug
tracker hardly converge on a clear picture.  CEP are meant to produce clear
design documents that can be discussed at a working group, commented by Coq
users, implemented and finally used as a reference.

A CEP is a document like this one.  Useful fields in the header are Title,
Drivers (people interested in the proposal and working on it) and Status.
Status shall be one of Draft, Candidate, Accepted, Rejected, Obsolete.

## A CEP's life
During a rainy day you have a great idea? Make a CEP(e)! Write a simple draft,
a mock up of the syntax and an intuitive description of the semantics. Tell
your colleagues. Other insiders may get interested. Then work out more details,
and when the CEP is understandable make it public: coqdev or coqclub or both 
depending on the subject of the CEP. Follow the discussion, comments, and update
the CEP.  When you feel things have settled, mark the CEP as a Candidate and
bring it to the working group. The discussion at the working group may lead to
more iterations in the design process, or Accept the CEP or Reject it.  Also
a CEP may become irrelevant, obsoleted by the circumstances.

Then start implementing it, or find someone that does it.

## More concretely, what should a driver do
1. write the draft, make a PR on https://github.com/coq/ceps
1. drive the discussions around it (on coq-club, coqdev, on the PR itself)
1. summarize the outcome in the CEP, and keep the document updated
1. defend it at the working group
1. eventually write code or find someone that does it

## FAQ
* *Why not a pull request (to https://github.com/coq/coq with the code)?* A CEP is about the design, and has to happen before code is written. A proof of concept (a toy implementation) is perfectly fine and may help the discussion. Still, pull requests on https://github.com/coq/coq are meant for code to be integrated, not for ideas to be discussed.
* *Why not a bug tracker entry? Why not a mailing list thread?* A CEP can be related to a bug number and discussion can happen on a mailing list.  A CEP summarizes the discussion into a more accessible document.  If you want to bring someone in the discussion a CEP is a single pointer to give to him.

## Changes
* 14/4/2016, first draft
* 24/1/2017, more details on the workflow

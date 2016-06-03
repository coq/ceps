Title: ''CEP(es), Coq Enhancement Proposal''

Drivers: ''Enrico''

Status: ''Draft''
----

This document introduces CEP, documents describing the design of a feature
for Coq '''before''' implementing it.  Discussions on mailing lists or the bug
tracker hardly converge on a clear picture.  CEP are meant to produce clear
design documents that can be discussed at a working group, commented by Coq
users, implemented and finally used as a reference.

{{https://upload.wikimedia.org/wikipedia/commons/a/a3/Boletus_edulis_%28Tillegem%29.jpg||width=300}}

A CEP is a document like this one.  Useful fields in the header are Title,
Drivers (people interested in the proposal and working on it) and Status.
Status shall be one of Draft, Candidate, Accepted, Rejected, Obsolete.

== A CEP's life ==
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

== What should a driver do ==
 * write the draft
 * drive the discussions around it
 * summarize the outcome in the CEP, and keep the document updated
 * defend it at the working group
 * eventually write code or find someone that does it

== FAQ ==
 * Why not a pull request? A CEP is about the design, and has to happen before code is written
 * Why not a bug tracker entry? Why not a mailing list thread? A CEP can be related to a bug number and discussion can happen on a mailing list.  A CEP summarizes the discussion into a more accessible document

== Changes ==
 * 14/4/2016, first draft

- Title: Visual debugger for Ltac, et al

- Drivers: Jim Fehrle

----

# Summary

I propose the functionality for a visual debugger for Ltac and other tactic
languages and the general steps needed to implement it.  This might also be
extended to step through instrumented monads; unfolding and reduction steps as
in cbv; and subparts of SSR sentences.  I seek feedback on the general plan
rather than presenting a detailed design.  Some of the steps may merit their
own CEPs.

# Motivation

While Ltac amounts to a special purpose programming language, Coq provides
only primitive debugging capabilities for it.  An improved debugger will make
Ltac easier to use.  It will also help those learning Coq to better understand
the actions of compound tactics such as “rewrite H; apply lemma1”.

The current debugger works only in coqtop, accepting debug commands from stdin
separate from Coq’s parser.  It’s invoked by “Set Ltac Debug” and provides only
simple stepping functions--no breakpoints.  “Info” permits tracing a given Ltac
expression.

# Proposal

The improvements can be implemented progressively in roughly the order in which
they appear.  Simpler steps are listed first.  The endpoint, if all the
improvements are implemented, is an IDE-based visual debugger.

1. Add additional debugger commands:
- Set breakpoints using Ltac tactic names
- Display current breakpoints with an ID number, allow clearing by number
- List available tactic names for breakpoints with wildcarding
- Step into function/step over function/continue execution/step out of function
  TBD: how these interact with backtracking
- Show the call stack
- (feature) Automatically show the function name in the debugger prompt
- Print Ltac variables (and other data?)
- Display “Show Proof Diffs” info with only the diffs (to facilitate use with
  large proof terms)
- TBD: run for n seconds, then break on the next tactic

These could be added to the existing debug mode code.  Alternatively, we could
create a debugger mode for Coq’s parser, which could also allow users to invoke
some of Coq’s informational commands, but nothing that changes the proof state.

2. Preserve location information (file, line #, character) for each simple 
tactic in an Ltac expression. Store this information in .vo files and load
it when a file is Imported.  Permit setting breakpoints by file and
line number.  Permit displaying the location information as part of
the debugger prompt.

3. Support a terminal panel for IDEs akin to coqtop that permits entering debug
commands and viewing the results.  Input and output is appended to the panel
contents rather than clearing the panel.  If the debugger commands become a mode
of the Coq parser, this would also be useful for running existing information
commands that the user doesn’t want to embed in their proof script.  This is
likely considerably less work to implement than the visual debugger.  This step
could be skipped in favor of a visual debugger, which is likely more work.

4. A visual debugger, providing capabilities such as:
- Adding and removing breakpoints by clicking in the edit buffer
- A visual indicator in the edit buffer of where breakpoints are set
- Automatically positioning the edit buffer to display the line being debugged
- Keeping a stack of locations visited in the editor with a way to return to
  the previous position
- Tracking changes in the location of breakpoints as the user modifies buffers

I suggest we should support this first in CoqIDE.  If the visual debugger is
only available through the XML interface, that might motivate Proof General to
release a version that uses that interface.

5. SSR statements can have multiple subparts.  If each subpart is marked as a
possible breakpoint, it should be possible for users to step through each subpart
to better understand what Coq is doing.

6. It may be possible to step across monads in the OCaml code that make up
tactics.  While it would likely be difficult to get source file location
information for all monads at once, monads could be instrumented so that
stepping through a monad would return its source file location to the debugger,
at which point it could be used to set a breakpoint.  This may be helpful to
those working on those tactics or wishing to better understand what a tactic
does.  This could include stepping through unfolding and reduction steps such
as in cbv.

7. Add to the documentation considerable explanation of proof terms, with
examples of typical proof terms produced for common tactics.  This may help
users translate the effects of complex tactics into an equivalent series of
simpler, more understandable tactics or at least get a better idea of what
is going on.  (It would be better if this could be done automatically, but
that may be difficult to impossible.)

I’m willing to do at least #1 and #7, perhaps starting this winter.  I’d be
happy to have help for #3 and/or #4.

# Drawbacks

Breakpoints must be implemented with care to avoid a performance impact when
the debugger is not active.

# Alternatives

The major alternatives are described in the Proposal section.

# Unresolved questions


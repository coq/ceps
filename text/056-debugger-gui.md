- Title: Visual debugger: debugging in secondary script files

- Drivers: Jim Fehrle

----

# Summary

Proposes changes to CoqIDE's GUI layout and behavior to support stopping
the debugger in secondary script files (i.e. files other than the topmost
script), which may be requested by "step-in" requests or breakpoints in the
secondary file.

Discuses how to ensure that breakpoint locations shown in the GUI remain
consistent with those in processed or compiled code as the user edits the
source script(s).

# Analysis

## GUI

The simple 1:1:1 relationship between script panels, Messages panels and
coqidetop sessions/debuggers from [#13783](https://github.com/coq/coq/pull/13783)
is inadequate for stopping in secondary script files.  For example, suppose the
script being run in `primary.v` stops in a file it depends on, say `secondary.v`,
because the user did a "step-in" or the debugger reached a previously-set
breakpoint.  In this case, the GUI should show the buffer for `secondary.v` with
the Messages panel of `primary.v` rather than the Messages panel of `secondary.v`.
`secondary.v` has its own independent coqidetop session, which may also be in
the debugger.  The layout of the GUI needs to change to show this information in
an understandable way.  In addition, a visual debugger needs a panel to
automatically display essential information such as the call stack and variable
values.

The PR for this CEP includes a mockup of the changes.  The changes add a new set of
debugging tabs, identified by the name of associated toplevel script.  These
tabs will be visible when one or more sessions have entered the debugger.
Each debugger tab has two subtabs, one with the stack and variables, the other
with the Messages panel.  The Messages panel is not shown in its usual
location once the associated script has entered the debugger.

Debugger tabs are created the first time the debugger stops for a session.

The mockup is approximate; the look for the added panel will be like the rest of
CoqIDE.

TBD: The current layout suggests that the Errors and Jobs panels are one per
script rather than what I would expect (one per CoqIDE process).  If so, they could
be changed to be additional tabs next to the debugger tabs.

While not part of this proposal, [#14040](https://github.com/coq/coq/issues/14040)
would use less space for the Find/Replace panel.

## Breakpoint consistency

Maintaining breakpoint consistency after edits that move them
is straightforward when the debugger stops only within the primary script.  
CoqIDE can immediately update the location of breakpoints that appear
after the last processed statement.  Edits changing the location of
breakpoints before the last processed statement cause a roll back of
the proof state, so these updates can also be applied immediately.
(BTW, CoqIDE currently gets confused if the user edits before the last processed
statement when coqidetop is busy.  This will be fixed by prohibiting edits
to the script when coqidetop is busy.  See
[#13967](https://github.com/coq/coq/issues/13967))

In contrast, maintaining breakpoint consistency in secondary scripts is much harder.
For example, if a user edits a secondary script in CoqIDE, giving new locations for
breakpoints, those locations won't match those in the running session until the
secondary script has been recompiled and the session has been restarted.
While it may be feasible for CoqIDE to maintain and apply a mapping from original
breakpoint locations to changed breakpoint locations, that seems complex and perhaps
fragile.  Also, how do you highlight a stopping point when the associated statement
has been deleted from the editor (i.e. from a "step", not a breakpoint)?

Or consider the case in which two scripts both depend on `secondary.v`.
After starting the first script, the user modifies and recompiles `secondary.v`
and starts the second script.  To handle this case correctly, CoqIDE would need
to maintain one mapping *per session*.

On the other hand, we shouldn't go out of our way to support multiple
simultaneous debug sessions--following a single debug session already requires
very close attention by the user.

A far simpler though restrictive way to ensure consistency is to
support a "multifile project" mode in which the user designates one script as
primary.  All other scripts would become read only until the user closes the
associated debugger panel.  This could be useful if the user is not going to
make significant changes to the secondary scripts.  (If the user plans to make
many changes to a secondary script, they are probably better off inserting their
test code into that script and running it as the primary script--in which
updated breakpoint locations are not an issue.)

(Probably out of scope: It would be helpful to have an easy way to reload script files
that have been modified by external editors.  Similarly, it would be helpful
to have an easy way to restart sessions that use stale versions of compiled
modules--perhaps re-running them up to the last stopping point. And/or providing
a way to check for stale scripts or compiled modules.)

For now, the simplest approach is not to do anything extra for secondary scripts,
instead clearly documenting the limitations and best practices for using
the debugger.  I recommend we take that approach initially.  We can always
do more later on.

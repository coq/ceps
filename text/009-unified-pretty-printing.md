- Title: Towards a new document type for Coq.

- Driver: Emilio J. Gallego Arias (@ejgallego),
  _co-drivers proposed by Emilio_: Hugo Herbelin (@herbelin), Pierre-Marie Pédrot (@ppedrot), Clément Pit--Claudel (@cpitclaudel), Enrico Tassi (@gares)
  (_this document is based on many discussions with them_)

- Status: Request For Comments, Pre-Implementation Draft

----

# Summary

Coq pretty printing was designed for a console-based setup, however
the situation these years has much changed and rich layout formats are
the norm.

We propose to enrich and consolidate the current `Pp.std_cmdpps` data
type into a more general document type. In particular we propose:

- To make `Pp.std_cmdpps` serializable, allow UI to render it. This
  allows for client-side reflowing and line-breaking.
- To merge "rich" printing into the `Pp` datatype, leading to the
  removal of `Richpp.richpp`.
- To enrich `Pp.std_cmdpps` with Coq-specific capabilities. For instance,
  define tags to mark implicit arguments, notation boxes (removing
  `Ppextend`), etc...
- To replace the current tagging system by a canonical, serializable one.
- To remove console specific printing command such as `Set Printing Width`.

This proposal has the potential to allow a great cleanup in the
code. For instance, serialization of `Pp.std_cmdpps` would allow to
implement `coqtop` as a feedback client.

**current printing path**

Coq does:

```ocaml
Feedback.msg_* : std_cmdpps -> unit =>
  if `log_via_feedback` then
    render_to_richpp;  [kinda hacky, can't use tag content]
                       [This forces settings like printing width!]
    send_feedback
  else
    dispatch_to_logger [emacs/color/normal]
    [duplicated path for colors, different tag system from `Pp`]
```

Clients do:

- _console loggers_ => call `Pp.pp_with` to convert `std_cmdpps` to
  `Format` commands. It uses the options
- _feedback_clients_ => custom render of `Pp.richpp`, mostly removing
  useless boxing.

**proposed printing path**

Coq does:

```ocaml
Feedback.msg_* : std_cmdpps -> unit =>
  send_feedback
```

Clients render `std_cmdpps`. Coq provides standard renderers to
`out_channel`, `string`, (maybe `rich_string` == string with colors?)
and `html`. Compatibility is preserved by `string`.

Clients chose rending options such as printing width, etc...

## Use cases and motivation:

We detail some concrete use cases to illustrate the approach:

- **Client-side reflowing**: CoqIDE/jsCOQ can now easily adapt display
  width without a roundtrip. They will receive/store the message in
  `Pp.std_cmdpps` formats, and when their UI refresh function is
  called they can just use the renderer. CoqIDE will likely call the
  `rich_string` renderer, jsCoq can fully delegate to the browser
  engine!

- **Implicit arguments display on hover**: Now implicit arguments are
  rendered but with tag implicit. jsCoq can for instance map the
  implicit tag to a css `display: none` property, but show the
  arguments on hover.

- **Rich notation display**: A common request by IDEs is to
  interpreted notations in a enriched way. Coq can now deliver
  notations to the UI in a way similar to the implicits. Thus the IDE
  can selectively disable notation display or custom render notations.

- **Accurate term location**: Every box can contain a path on the term.

- **Rich document types**: We can easily support tables, paragraphs,
  emphasis on text, math, etc...

### A hard problem:

_Mapping terms to documents and viceversa_

Indeed, the ideas in `Ppannotation` is right, however, I the
implementation seems quite difficult to use, in particular because the
content of the tags must be serialized again.

SerAPI can indeed display the full annotated output, I recommend doing
it and observing what you get. Go to https://x80.org/rhino-hawk/, wait for the libraries to load, then type:

```lisp
(Control (StmAdd () "Require Import Coq.Init.Prelude. Goal forall n, n + 0 = n. intros n."))
(Control (StmObserve 4))
(Query ((pp ((pp_format PpAnn)) )) Goals)
```

My impression is that the current mix of richpp and annotations is too
disjoint to be useful (you get either a string or the full blown
`constr`, IDEs want something _in the middle_). So in a sense, what it
is below is a reification of such "PpAnn" output.

### Example of current `richpp` output vs desired output.

Current:
```lisp
Eval hnf in 2 + 2.
(Element
 (_ ()
  ((PCData " = ")
   (Element (constr.reference ()
            ((PCData "S"))))
   (PCData " (1")
   (Element (constr.notation ()
            ((PCData" +"))))
   (PCData" 2)\n : ")
   (Element (constr.reference ()
            ((PCData nat)))))))
```

Desired [simplified]:
```lisp
(hovbox
 (appbox
  (tag cons "S")
  ((notbox
     (infixbox "+"
       (tag num 1)
       (tag num 2))
     (appbox
       (tag ref "addn")
       ((tag num 1)
        (tag num 2))))))
  (tag null " : ")
  (tag type "nat"))
```

## Summary of plan:

The plan can be implemented gradually, each of the steps is in itself
a milestone and could be done over several releases.

1. Remove current tagging mechanism (PR#185): We couldn't identify
  users for tags other than a string, thus remove.
1. Now we can make `Pp.std_cmdpps` serializable, do it. Clean up the
  logger vs feedback distinction, fully encapsulate console access.
1. Remove richpp.
1. Implement richer tagging: first example, output implicit
  arguments. (This can still be disabled for performance)
1. Add notation support to `Pp.std_cmdpps`. Remove `Ppextend`.


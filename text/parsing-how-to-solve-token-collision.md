- Title: Towards a local lexing of sequences of symbols in order to prevent collisions in remote parts of the grammar
- Driver: Hugo
- Status: Draft

# Summary and motivation

Tokens made of sequences of symbols such as `||` or `|}` as recognized at lexing time, and it may break parsing of expressions such as `intros [||]` or `{x & P #|x|}` where the same sequences of symbols are supposed to be interpreted as distinct symbols, even though there is no local parsing conflict. This proposal is about collecting ideas in direction to move the lexing of sequences of symbols at parsing time and fix the limitation.

# Basic ideas

## Lexing only remembers when sequences of symbols are contiguous; keywords recognition is done at parsing time

We introduce two kinds of keywords: `KEYWORDWAIT` and `KEYWORDEND`. At lexing time, any sequence of symbols is translated into a sequence of tokens with only the last symbols marked as `KEYWORDEND`. For instance, `|}` is translated to `KEYWORDWAIT '|'; KEYWORDEND '}'`.

At the time of compiling grammar rules (`GRAMMAR EXTEND`, `TACTIC EXTEND` in `coqpp` or `Notation`, `Tactic Notation` in `pcoq.ml`), the same sequence of symbols, say `"|}"`, is similarly translated into the same sequence, say `KEYWORDWAIT '|'; KEYWORDEND '}'`.

At parsing time, any time a `KEYWORDEND` is expected but a `KEYWORDWAIT` is found, the later is accepted as if the original string had had an extra space after the first symbol, i.e. as if `| }` had been given instead, i.e. as if the lexer had returned ``KEYWORDEND '|'; KEYWORDEND '}'`. The parsing then continue on the remaining stream.

At parsing time, any time a `KEYWORDEND` is expected and a `KEYWORDEND` is actually found, the symbol is also consumed and parsing continue on the remaining stream.

## Dealing with distinct parsing levels recognizing sequences of symbols sharing a common prefix

Let's assume an entry `constr` with a subrule `SELF; "some-sequence-of-symbols"` and, at a lower level, a subrule presenting an (optional) subrule starting with a prefix of the same sequence of symbols. A typical example is:
```
constr: [
"80" [ SELF; "/\"; NEXT ]
"40" [ SELF; "/"; NEXT ]
]
```
where we want `x /\ y` not to give a syntax error after having found `/`.

Two solutions are candidate for further exploration. The first is to introduce duplication at compilation time of the grammar so that the grammar is actually compiled into:
```
constr: [
"80" [ SELF; "/\"; NEXT ]
"40" [ SELF; "/\"; constr LEVEL "79" ]
     | SELF; "/"; NEXT ]
]
```
The replication at a lower level of the suffix of a higher level rule starting with a long token should be done everywhere a subsequence of the long token can be parsed in parallel to recognizing the empty stream. This could be done Coq side for `Notation` and `Tactic Notation` or `coqpp` side for the various `EXTEND`. This could also be done directly in `gramlib` in the `Grammar.srules` compilation function.

The second solution is to work at execution time (in the `Grammar.parser_of_tree` function) and propagate to the lower level the list of sequences of symbols that are accepted at the higher level. As above, at the time of parsing a sequence made of some (possibly none) `KEYWORDWAIT` followed by a `KEYWORDEND` in parallel to being able to recognize the empty stream, a check is made that the same sequence of symbols is not a prefix of the list coming from above. If it is, control is given back to the upper level.

## Notes

In a first step, we exclude from this protocol tokens mixing symbols and characters, such as, e.g. `=_N`.


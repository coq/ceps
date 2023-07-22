- Title: Towards a more flexible and accurate model for grammar levels and associativity

- Drivers: Hugo Herbelin

----

# Summary

The Camlp5/gramlib model for associativity of levels in extensible grammar has a couple of issues. We reflect how to solve them.

# Detailed description of the current problems

## Non associativity

Camlp5 let us believe that non associativity is possible and we let Coq users believe in turn that it was the case too. However, non associativity is *not* a feature of Camlp5. As said in the section [Associativity](https://camlp5.readthedocs.io/en/latest/grammars.html?highlight=associativity#extensible-grammars) of the Camlp5 manual, the keyword `NONA` behaves as `LEFTA`. And indeed, there is no mechanism to support nor emulate non associativity of infix or postfix operators in Camlp5.

Also, non associativity (equivalently right associativity) is inactive on postfix operators (e.g., a rule such as `[ RIGHTA [ t = SELF; "!" -> ... ] ]` accepts parsing `x!!`. This is for the same reason as non-associativity is not supported (one would need to call continuations only once and not arbitrarily recursively many often, see remark at end of camlp5/camlp5#100).

For another reason, non associativity (equivalently left associativity) is not emulable on prefix operators (e.g., a rule such as `[ LEFTA [ "?"; t = SELF -> ... ] ]`, or `[ LEFTA [ "?"; t = NEXT -> ... ] ]`, accepts parsing `??x`); this times it is because of a fallback which replace `SELF` by `SELF TOP` if `SELF` has failed.

Note that the non support for non associativity in the parser is currently a cause of asymmetry with the printer, since the printer respects non associativity.

## Each Camlp5 level is in practice two levels

Indeed, a Camlp5 level is made of two blocks:
- a block of rules of the form `SELF; suffix`
- the block of rules not of this form

In the first block, `SELF` is implemented by a call to the 2nd block of rules. As a consequence, if an infix notation is put at Coq's lower level 0, it still succeeds to parse its argument by finding closed subterms in the second block of level 0, such as an ident, or `( term )`.

This results in bug reports such as coq/coq#15336 where the parser parses the notation but the printer does not print it.

## Mixing associativity in the same level is technically possible and would solve the issue of combining developments that set different associativities to the same level

In practice, a level can mix different associativities. If a rule of the form `SELF; "+"; NEXT -> ...` is put in a right-associative level, it parses `+` in a left associative way. And if a rule of the form `SELF; "+"; SELF LEVEL "foo" -> ...` is put in the left-associative level `"foo"`, then, `+` is parsed in a right associative way. This is because the *only* effect of the `RIGHTA`/`LEFTA` keywords at some level, say `"foo"`, is to give a *default* interpretation to the occurrences of `SELF` on the right-hand side of rules (that is such `SELF` is then interpreted as `NEXT` for `LEFTA` and as `SELF LEVEL "foo"` for `RIGHTA`). In particular, we can decide the associativity per rule by just not using `SELF` on right-hand sides.

Note that in this case, rules with right associativity (i.e. ending with `SELF LEVEL "foo"`) yield precedence (i.e. bind wider) than rules with left associativity.

See e.g. coq/coq#17859 and camlp5/camlp5#100 for more details.

Note that an example of conflicts on setting different associativities to the same level is told to be when combining Iris and MathComp.

## Camlp5 associativity shown with `Print Grammar constr` leads to confusion

The `RIGHTA`/`LEFTA` status of a level is thus indicative, and not constraining. And, actually, Coq do override it by setting itself the right-hand side of rules to `NEXT` or `SELF LEVEL "foo"`.

When no official associativity is assigned to a level, Camlp5 decides it is left associative while the Coq table decides (confusingly) that it is right associative. Since the associativity is only a default value for rules which can be overriden per rule, one confusingly sees a level reported as left associative while Coq allows to add only right associative rules to the level (see coq/coq#12373).

Also, the current Camlp5 implementation does not treat associativity in the presence of `LIST1` and `LIST0` on the border of a rule. E.g., in `...; LIST1 SELF -> ...`, `SELF` is interpreted as `SELF TOP` and thus does not follow associativity. This is visible e.g. in the `"choice"; LIST1 rewstrategy` rule for `rewstrategy`.

## Camlp5/gramlib does not fully respect levels

When no rule matches, there is a recovery mechanism (see coq/coq#9008) made of 4 fallbacks that bypasses the level specified by the user.

For instance, `True \/ forall x, x = 0` is tolerated even though `forall` is at level 200 and `/\` at level 80. Or `x~0%Z` is tolerated even though `%Z` expects its arguments to be at level 1.

# Proposal

We propose to go towards a new model:
- that respects levels
- that respects no associativity
- is more flexible about mixing different associativities in the same level
- remains mostly compatible with the existing situation

# Solutions

## Removal of the recovery mechanism

Removing the recovery mechanism breaks quite common situations such as `True \/ forall x, x = 0`, or `2^-n`, or `x~0%Z`.

One could try to automatically adapt the scripts but I believe that the simplest is to move `forall` (and all `binder_constr` rules spanning until the end of the sentence) to a lower level, such as 10, just above the level of application.

The drawback is that we need to modify the printer so that it knows how to print such cycle made of a rule at some level (here 10) which is lower than the level on the right-hand side of the rule (here 200). This is however already made possible by PR #17875.

For `-`, there are several solutions, such as:
- to set it at level 10 with arguments at level 40 (the level of `*`) so that `2 ^ - x * y` is `2 ^ - (x * y)` but `2 ^ - x + y` is `(2 ^ - x) + y` (??)
- to change scripts and add parentheses

For `x~0%Z`, there are hopefully few occurrences.

## Granting non associativity

In our experience, the changes are relatively small in the standard library:
- it impacts the family of notations `=`, `=?`, `<`, `<?`, etc. at level 70
  - one solution is to add parentheses in a couple of expressions of the form `x =? y = z` (namely so that it is `(x =? y) = z`)
  - other solutions would be to move `=?` to a lower level (and higher precedence) but I did not investigate the impact
- it impacts `mod`, currently set non associative at the left-associative level 40 and this would either require to move it to another level, or to set it left-associative, or to accept different associativities in the same level

## Fixing the associativity bugs and supporting different associativities in the same level

There are basically two directions:
- to renounce to Camlp5 support for levels, that is, to manage manually the inclusion of levels and the associativity of operators using distinct entries
- to fix the problems of levels and associativity in Camlp5

The first direction would a priori require more work and more support of Coq to manage itself the levels and associativity. On the other side, an advantage is that it would then probably be easier to experiment with different parsing engines.

The second direction would have the advantage to be benefital to all users of Camlp5 in general. Moreover, I already implemented some pieces of it, so that would be more satisfactory for me.

For the second direction, what needs to be done is:
- to support deactivating the recovery mechanism: this is done in coq/coq#17876
- to support non-associativity: this is done in coq/coq#17876, and I roughly see how to extend it with a model of per-rule associativity
- to fix a small asymmetry in the definition of `NEXT` level in Camlp5 (see camlp5/camlp5#100)
- to support per-rule associativity: I already have a branch started for it

  Altogether, in the resulting model, each Camlp5 level is made of five levels of increasing precedences in this "natural" order:
  - the level of right-associative infix operators (starting with `SELF` and ending with `SELF`)
  - the common level of left-associative infix and postfix operators (starting with `SELF` and with repeatable continuation)
  - the common level of non-associative infix and postfix operators (starting with `SELF` and with a non-repeatable continuation)
  - the level of right-associative prefix operators (starting with a terminal and ending with `SELF`)
  - the common level of closed expressions and non-associative prefix operators (starting with a terminal and w/o recursivity on the right)

  even if other orders can be considered too.

All in all, the proposal would:
- Solve printing bugs: coq/coq#15336, via the modified coq/coq#15341
- Solve oddities: recovery mechanism, coq/coq#12373 and coq/coq#15781
- Support combining theories with incompatible associativity at the same level
- Provide non associativity

## Appendix

### A summary of inconsistencies between the parser and printer

- when the underlying grammar is not stratified as in the case of `rewstrategy` that PR coq/coq#17832 fixes, or if `binder_constr` or `-` were moved at lower levels
- when a rule is declared non-associative (since the parser does not respect non-associativity)
- when an infix is put at level 0 (see coq/coq#15536) or more generally when a left-associative rule refers to the non-self-starting subset of a rule

### A summary of changes to be done

Regarding PRs:
- renounce to unmerged [#15341](https://github.com/coq/coq/pull/15341) that is, do not forbid infix operators at level 0 and inform instead the printer that a level is made of sublevels
- renounce to unmerged [#17126](https://github.com/coq/coq/pull/17126), that is, no need any more to move to level 1 the prefix/postfix notations at level 0

In the Coq wrapper to Camlp5:
- stop forbidding to declare at some level an operator whose associativity is different from the one already registered for a level
- continue implementing associativity of operators by using either `NEXT` or `SELF LEVEL foo` without further qualms of not relying on the default associativity mechanism (or better: implement per-rule associativity in Camlp5)
- continue accepting that a level host rules referring to an arbitrary higher level on its right-hand side (to support `binder_constr` or `-` at level 10)

In the mlg files and their reflection in `egramcoq.ml`:
- make the levels in `egramcoq.ml` consistent with `g_constr.mlg` (for `term` at levels `0`, `8` and `9`), so that if a notation open on both sides and without explicit associativity at level 8 or 9 works at it does currently

In the Coq reference manual:
- make explicit that different associativities can coexist in the same level
- make explicit that the associativity of a level is only used as a default
- make clearer that the associativity written by `Print Grammar` is only to assign a default associativity for rules mentioning `SELF` on their right-hand side
- document that `ARGUMENT EXTEND` is in practice set to `LEFTA`

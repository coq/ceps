- Title: Giving access in `match` to the expansion of the term being matched via an alias in order to support more fixpoints

- Drivers: Hugo Herbelin

----

# Summary

We propose to extend the context of each branch of `match` in the Calculus of Inductive Constructions with an alias referring to the constructor of the branch, so that more fixpoints are available in a "natural" way.

# Motivation

When writing fixpoints in inductive types with indices, there is a standard conflict between referring to the expansion of a variable being matched (so that its type corresponds to the type in the branch) or referring to the variable so that it is compatible with the guard when the fixpoint is later used in another fixpoint. A typical example (even without indices) is `Nat.sub`:
```coq
Fixpoint sub (n m : nat) {struct n} : nat :=
  match n with
  | S k, S l => sub k l
  | _, _ => n
  end
```
where it is important that `n` is not expanded.

The proposal is to resolve this conflict by giving an explicit name to the expansion of the term being matched in a branch so that the guard condition knows that it is a decreasing argument and not a constructor disconnected from the term being matched. For instance, `Nat.sub` would be written:
```coq
fix sub (n m : nat) {struct n} : nat :=
  match n, m with
  | S k, S l => sub k l
  | _ as n', _ => n'
  end
```

In the case of an inductive type with no indices, this does not provide much, but the situation changes for type families. For instance, imagine we want to apply parametricity to `Nat.sub`. That would give:
```coq
Fixpoint is_sub (n : nat) (Pn : is_nat n) (m : nat) (Pm : is_nat m) : is_nat (Nat.sub n m) :=
  match Pn in (is_nat n) return is_nat (Nat.sub n m) with
  | is_O => is_O
  | is_S x P_ =>
      match
        Pm in (is_nat m0)
        return is_nat (match m0 with 0 => S x | S l => Nat.sub x l end)
      with
      | is_O => is_S x P_
      | is_S l Pl => is_sub x P_ l Pl
      end
  end.
```
where, for typing, we have to expand `Pn` into a constructor in the right-hand side.

With the proposed extension, we would write:
```coq
Fixpoint is_sub (n : nat) (Pn : is_nat n) (m : nat) (Pm : is_nat m) : is_nat (Nat.sub n m) :=
  match Pn in (is_nat n) return is_nat (Nat.sub n m) with
  | is_O as p => p
  | is_S x P_ as p =>
      match
        Pm in (is_nat m0)
        return is_nat (match m0 with 0 => S x | S l => Nat.sub x l end)
      with
      | is_O => p
      | is_S l Pl => is_sub x P_ l Pl
      end
  end.
```
with `p` of the same type as the constructor but recognized as a subterm for the guard condition.

# Details about the design

For an inductive type `[... Ii : Δi -> si := {... Cij : Ωij -> Ii δij ...} ...]`, the proposed new typing rule is:
```
  Γ ⊢ t : Ii δ     Γ, y : Δi, x : Ii y ⊢ P : s    ... Γ, z : Ωij, w : Ii δij  ⊢ uij : P[y,x:=δij,Cij z] ...
  ————————————————————————————————————————————————————————————————————————————————————————————————————
                Γ ⊢ (match t as x in Ii y return P with ... Cij z as w => uij ... end) : P δ
```
Then, for the guard condition, the new variable `w` is considered of the size of `t`.

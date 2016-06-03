- Title: Numeral Notation

- Driver: Daniel

- Status: Draft

-----

# Summary

Numeral Notation is a new proposed vernac command. It allows any Coq user to define his own numeral types to be parsed and printed as strings of decimal digits, possibly prefixed by a minus sign (such as "0", "-42", "825"). There is an implementation of that, but before integrating it into the Coq sources, there are several decisions to take. But let us see what it is.

First, the type of "strings of decimal digits" has been named Z' (Z prime, there is an debate about this choice, see below). The vernacular command is the following:

```
Numeral Notation t f g : t_scope { (printing** <list of references>) } { (warning after <number>) }
```

* t is the type,
* f is a function of type "Z' -> option t"; when a string of digits is found in the scope of t, the function Z' is called; if its return is "Some v", the value is v; if it is "None", this is an error, for example "(-1)%nat",
* g is either a function (of type "t -> option Z'"), or a Ltac (depending on the option **printing**: see below),
* t_scope is the scope of t,
* the optional **printing** allows to specify a list of reference names to be printed; if t is an inductive type, it could be its constructors, or some of its constructors; if this option is absent, the default is all its constructors; in that case, g must be a function of type "t -> option Z'"; if t is not an inductive type, this list must be the names of the terms or functions (typically axioms) to be printed; for example, for the type R, it has been defined as "R0 R1 Rplus Rmult Ropp"; in that case, g must be an Ltac returning a value of type Z' or failing by "fail". If the result of g is "None" or "fail", the value is not printed as strings of digits.
* the optional **warning after** is to print a warning if the string of digits represents a too big number; typically used for the type "nat" which is very expensive in memory resulting on stack overflow or memory fault if a too big value is given. For nat, it has been defined as 5000; Test "Check 5000%nat." (no warning) and "Check 5001%nat" (warning) on the toplevel.

This implementation has as objectives:

 * to try to be the most possible compatible with the current version (which used plugins written in OCaml), and
 * to give Coq users a useful feature.

## Example

```
Fixpoint pos'pred_double x :=
  match x with
  | x'I p => x'I (x'O p)
  | x'O p => x'I (pos'pred_double p)
  | x'H => x'H
  end.

Definition nat_of_Z' x :=
  match x with
  | Z'0 => Some O
  | Z'pos p =>
      let fix iter p a :=
        match p with
        | x'I p0 => a + iter p0 (a + a)
        | x'O p0 => iter p0 (a + a)
        | x'H => a
        end
      in
      Some (iter p (S O))
  | Z'neg p => None
  end.

Fixpoint pos'succ x := 
  match x with
  | x'I p => x'O (pos'succ p)
  | x'O p => x'I p
  | x'H => x'O x'H
  end.

Definition Z'succ x := 
  match x with
  | Z'0 => Z'pos x'H
  | Z'pos x' => Z'pos (pos'succ x')
  | Z'neg x' =>
      match x' with
      | x'I p => Z'neg (x'O p)
      | x'O p => Z'neg (pos'pred_double p)
      | x'H => Z'0
      end
  end.

Fixpoint Z'_of_nat_loop n :=
  match n with
  | O => Z'0
  | S p => Z'succ (Z'_of_nat_loop p)
  end.

Definition Z'_of_nat n := Some (Z'_of_nat_loop n).

Numeral Notation nat nat_of_Z' Z'_of_nat : nat_scope
  (warning after 5000).
```

## Debate
 * Z' is defined exactly like Z, with a positive' and constructors having having a quote. So why not using Z? Z' having to be defined very early in the Coq library (Datatypes.v), to be used in the definition of nat (Nat.v), we could move the definition of Z and positive into Datatypes.v and so, we do not have two definitions Z and Z'. I think Z' should be kept, perhaps with another name, for the following reasons:
  * For the mathematical point of view, there is no reason to define ℤ before ℕ. A mathematician using Coq would find this strange. For me, Coq is like a new Bourbaki, thinks must be clean as far a mathematics are concerned, and there is no reason to change this order of definitions just for a parsing and printing issue;

  * Z' is now defined like Z, but it is not a definition of integers; it is a definition of string of decimal digits; it is necessary for programming issues, not for mathematical issues; its definition may change if we decide to be able to parse and print decimal numbers (e.g. 3.5), or even rings in general (e.g. polynomials), as it was suggested in the Coq working group;

  * If we move the definition of Z into Datatypes.v, do we move also their associated comments explaining its implementation? Do we have to move all Z functions? Or kept them where they are now? In that case, Z definitions, functions, and proofs would be separated in different parts of the Coq library;

  * Z is very important, Z' is a detail; they should not be considered as the same thing

 * It was suggested to define Numeral Notation for R differently, since the way integer numbers were coded for R was not good; I think that compatibility is important; if R users want reals integer numbers be parsed and printed differently, they can use their own "Numeral Notation" vernac command (in that case, it masks the "Numeral Notation" of the library), test if it is really better and later, we could adopt a new implementation of real integers.

 * The system have been implemented also for int31, bigN, bigZ and bigQ; actually, I think that they should eventually been excluded from this system, because for these types, there are very important issues for speed and memory usage; in this new implementation, there is a big difference (I tested for 10^1000) and it it 4 times slower than the previous version and I suspect this could be worse for bigger numbers.

 * Speed of parsing and printing for the other types (nat, Z, R) should be tested, but it depends whether Coq programmers use really big numbers of these types; if not, we could have this version which is probably slower that the previous one, but small compared to the other parts of Coq (e.g. tactics).

 * Pierre Letouzey : I suggest to use a very simple base-10 encoding as Coq entry point of Daniel's new parsing/printing mechanism, and let Coq do the rest of the conversion between these base-10 numbers and nat/positive/N/Z/. A [proof-of-concept](https://github.com/letouzey/baseconv) is on github.

  * Interest:

   * Less uncertified critical code : during parsing at the OCaml level, we could keep numeral constants as strings (e.g. "123"), and simply convert these strings to Coq lists of base-10 digits, i.e. D1::D2::D3::nil in my first datatype proposal, see [Deci.v](https://github.com/letouzey/baseconv/blob/master/Deci.v), or (D1 (D2 (D3 Stop))) in the second datatype proposal in [DeciBis.v](https://github.com/letouzey/baseconv/blob/master/DeciBis.v).

   * This way, we could get rid of arbitrary sized numbers on the OCaml side (typically our lib/bigint.ml and its potential bugs).

   * On the opposite, all conversions functions are already proved in Coq to be bijections, see for instance [DeciProofs.v](https://github.com/letouzey/baseconv/blob/master/DeciProofs.v).

   * These Coq proofs aren't needed by the runtime mechanism, they could be kept anywhere in the standard library, as a kind of safety check. On the opposite, the runtime functions require very little (an euclidean division function, mostly) and can come very early in the stdlib.

   * The same mechanism could also provide constants in hexadecimal notation :-), see [HexaProofs.v](https://github.com/letouzey/baseconv/blob/master/Hexa.v|Hexa.v]] and [[https://github.com/letouzey/baseconv/blob/master/HexaProofs.v).

  * Cons : Possible slow-up due to these conversions done via vm_compute (but preliminary tests looks promising, even between base10 and nat, see [Tests.v](https://github.com/letouzey/baseconv/blob/master/Tests.v)).

  * Todo :
   * Integrate with Daniel's mechanism
   * In particular extend to signed integers (i.e. add a boolean flag coding the sign)
   * Continue the speed tests
   * Many proofs to cleanup, this is a proof-of-concept, remember ;-)

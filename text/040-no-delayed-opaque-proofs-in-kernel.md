- Title: Opaque proofs don't belong to the safe_env

- Drivers: Enrico

----

# Summary

Opaque proofs morally play the role of a certificate for third party
verification or extraction. For type checking they are not needed, they
are akin to axioms.

This is the only reason why parallel processing is actually possible.
It is also key to refactoring of proofs (if you don't change the statement
you are not going to break things).

For various reasons opaque proofs are in the kernel. This CEP explains
how to put them elsewhere. This reduces the complexity of the kernel
and of the STM without losing functionality. 

# Motivation

The motivation is to: simplify STM and the way it handles the possible repair
of proofs. 

# Detailed design

## Mock up of the pre STM code (up to Coq 8.4)

```ocaml
type name = string (* absolute name *)
type constr = int
type types = int
let mkType = 0

module SafeTyping : sig

  (* The opaque type of checked env *)
  type safe_env
  val empty_env : safe_env

  (* The update function *)
  val add_constant :
    name -> constr -> types -> safe_env -> safe_env
  val add_opaque_constant :
    name -> constr -> types -> safe_env -> safe_env
  val add_axiom :
    name -> types -> safe_env -> safe_env

  (* breaks opacity abstraction: Print, Extraction *)
  val get_constant_body : safe_env -> name -> constr

end = struct

  type body = Transparent of constr | Opaque of constr | Axiom
  type safe_env = (name * (body * types)) list
  let empty_env = []

  let typecheck : safe_env -> constr -> types -> unit  = assert false

  let add_constant name t ty l =
    assert(not(List.mem_assoc name l));
    typecheck l ty mkType;
    typecheck l t ty ;
    (name, (Transparent t, ty)) :: l

  let add_opaque_constant name t ty l =
    assert(not(List.mem_assoc name l));
    typecheck l ty mkType;
    typecheck l t ty ;
    (name, (Opaque t, ty)) :: l

  let add_axiom name ty l =
    assert(not(List.mem_assoc name l));
    typecheck l ty mkType;
    (name, (Axiom, ty)) :: l

  let get_constant_body l n =
    match List.assoc n l with
    | Transparent x, _ -> x
    | Opaque f, _ -> f
    | Axiom, _ -> failwith "axioms don't have a body"


end
```

## Mock up of the current code (since Coq 8.5)

```ocaml
type name = string (* absolute name *)
type constr = int
type types = int
let mkType = 0
module Future = struct
  type 'a t = 'a Lazy.t
  let force = Lazy.force
  let chain f g = lazy (g (force f))
end

module SafeTyping : sig

  (* The opaque type of checked env *)
  type safe_env
  val empty_env : safe_env

  (* The update function *)
  val add_constant :
    name -> constr -> types -> safe_env -> safe_env
  val add_opaque_constant :
    name -> constr Future.t -> types -> safe_env -> safe_env
  val add_axiom :
    name -> types -> safe_env -> safe_env

  (* breaks opacity abstraction: Print, Extraction *)
  val get_constant_body : safe_env -> name -> constr

  (* ensures all proofs are checked, this is called ad the env to let
     proofs be eventually computed in the background, in parallel... *)
  val join_safe_env : safe_env -> unit

end = struct

  type body = Transparent of constr | Opaque of constr Future.t | Axiom
  type safe_env = (name * (body * types)) list
  let empty_env = []

  let typecheck : safe_env -> constr -> types -> unit  = assert false

  let add_constant name t ty l =
    assert(not(List.mem_assoc name l));
    typecheck l ty mkType;
    typecheck l t ty ;
    (name, (Transparent t, ty)) :: l

  let add_opaque_constant name f ty l =
    assert(not(List.mem_assoc name l));
    typecheck l ty mkType;
    (name, (Opaque (Future.chain f (fun t -> typecheck l t ty; t)), ty)) :: l

  let add_axiom name ty l =
    assert(not(List.mem_assoc name l));
    typecheck l ty mkType;
    (name, (Axiom, ty)) :: l

  let get_constant_body l n =
    match List.assoc n l with
    | Transparent x, _ -> x
    | Opaque f, _ -> Future.force f
    | Axiom, _ -> failwith "axioms don't have a body"

  let join_safe_env l =
    List.iter (function (_,(Opaque f,_)) -> ignore(Future.force f) | _ -> ()) l

end
```

Remark the changes
- from `constr` to `constr Future.t`
- from `typecheck l t` to `Future.chain f (.. typecheck..)`
- new `join_safe_environment` API to fully check a `safe_env`

The choice back then was to be very conservative in the kernel, and just
sprinkle `lazy` here and there (`Future.t` was like lazy but with some wrapping
to deal with imperative code).

## New code (this CEP)

```ocaml
type name = string (* absolute name *)
type constr = int
type types = int
let mkType = 0
(* no Future.t *)

module SafeTyping : sig

  (* The opaque type of checked env *)
  type safe_env
  val empty_env : safe_env

  (* The update functions *)
  val add_constant :
    name -> constr -> types -> safe_env -> safe_env
  val add_opaque_constant :
    name -> types -> safe_env -> safe_env
  (* no need for add_axiom *)

  (* breaks opacity abstraction: Print, Extraction *)
  val get_constant_body : safe_env -> name -> constr

  (* justifications for opaque_constants *)
  type opaque_proof = Missing | Proof of constr

  (* This time it should be probably called validate_safe_env *)
  val join_safe_env : safe_env ->  opaque_proof list -> unit

end = struct

  type body = Transparent of constr | Opaque
  type safe_env = (name * (body * types)) list
  let empty_env = []

  let typecheck : safe_env -> constr -> types -> unit  = assert false

  let add_constant name t ty l =
    assert(not(List.mem_assoc name l));
    typecheck l ty mkType;
    typecheck l t ty ;
    (name, (Transparent t, ty)) :: l

  let add_opaque_constant name ty l =
    assert(not(List.mem_assoc name l));
    typecheck l ty mkType;
    (name, (Opaque, ty)) :: l

  let get_constant_body l n =
    match List.assoc n l with
    | Transparent x, _ -> x
    | Opaque, _ ->
        failwith "opaque proofs are not in the kernel, search opaque tables"

  type opaque_proof = Missing | Opaque of constr

  let rec join_safe_env l p =
    match l, p with
    | (_,(Transparent _,_)) :: l, p -> join_safe_env l p
    | (name,(Opaque,ty)) :: l, Missing :: p ->
          prerr_endline (name ^ " is an axiom")
    | (_,(Opaque,ty)) :: l, Proof t :: p ->
          typecheck l t ty;
          join_safe_env l p
    | _ -> failwith "wrong opaque proofs list"

end
```

Remark:
- no `Future.t`, no `lazy`
- proofs are not in the safe_env (cfr Indirect/OpaqueTable & lazy loading)
- the asynchronous computation of proofs is totally unknown to the kernel,
  it is the upper layers, eg STM, that pass to it an opaque_proof list
- one can join/validate a safe env many times, with more or less axioms
  (today you can't easily change your mind from Qed and Admitted)
- Elephant in the room: modules/functors tamper with opaque proofs

# Alternatives

Isabelle does what we do now (via promises), but does not let one
repair a proof (you simply redo it from scratch).

# Unresolved questions

### Universes (eventually vio)

For printing/typing purposes the universe constraints are inside the body
of opaque constants.

In the new model join_safe_env could be in charge of:
- putting the constraints there, next to the type
- retuning an updated safe_env

To be understood is what we do for the libobject action of an opaque
constant. Today the constraints are there, but lazily. In vio mode they are
not, but then when one turns the vio to vo the are saved in an explicit segment
and loaded by the action IIRC (since patching the libobject part of the .vo is not easy).


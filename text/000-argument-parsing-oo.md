- Title: Structure and share command line arguments among components and tools

- Drivers: Enrico

----

# Summary

Coq ships many binaries: coqc, coqtop, coqdep, coqdoc, coqide.
As well a few technical binaries: stmproofworkertop, ...
Coq is made of components that are parametrized by sets of options.

We propose an approach (and a POC library) to:
- declare options together with their documentation
- groups options into sets, corresponding to component or tools
- these sets can be freely combined, eg reused
- components API can declare the set of options they understand
- subtyping automatically shrinks a set of options to fit an API, if wanted 

# Motivation

Today we lack a proper infrastructure for:
- sharing parsing options and documentation across components/tools
- organize/structure options in coherent sets

Documentation is not at the same place where the option syntax is
declared. The usage messages get out of sync.

# Detailed design

```ocaml
(* engine ------------------------------------------------------------ *)


(* type of flags, to share parsing/printing among flags *)
type t =
 | Flag of (unit -> unit)
 | Bool of (bool -> unit)
 | String of (string -> unit)
 | Enum : (string * 'a) list * ('a -> unit) -> t

let coq_bool_of_string = function
  | "yes" | "on" | "true" -> true
  | "no" | "off" | "false" -> false
  | _ -> failwith "not a boolean"

let mk_parser k t l =
  match t, l with     
  | Bool f, x :: y :: rest when x = k -> f (coq_bool_of_string y); Some rest
  | Flag f, x :: rest when x = k -> f (); Some rest
  | String f, x :: y :: rest when x = k -> f y; Some rest
  | Enum (vals,f), x :: y :: rest when x = k ->
      f (List.assoc y vals); Some rest
  | _ -> None

let mk_printer s d t fmt () =
  Format.pp_print_string fmt s;
  Format.pp_print_tab fmt ();
  Format.pp_open_box fmt 0;
  begin match t with
  | Flag _ -> ()
  | Enum (vals,_) ->
      Format.pp_print_string fmt "(";
      let vals = List.map fst vals in
      let x, xs = List.(hd vals, tl vals) in
      Format.pp_print_string fmt x;
      List.iter (Format.fprintf fmt "|%s") xs;
      Format.pp_print_string fmt ") "
  | String _ -> Format.pp_print_string fmt "<string> "
  | Bool _ -> Format.pp_print_string fmt "<yes/no> " end;
  Format.pp_print_text fmt d;
  Format.pp_close_box fmt ();
  Format.pp_print_tab fmt ()
;;

(* collection of options to be parsed or printed *)
class registry = object(self)
  val mutable parsers = []
  val mutable printers = []
  val mutable max_len = 10
  val mutable keys = []
  method register s d t =
   if not (List.mem s keys) then begin
     keys <- s :: keys;
     parsers <- mk_parser s t :: parsers;
     printers <- mk_printer s d t :: printers;
     max_len <- max max_len (String.length s)
   end
    
  method parse l =
    let rec aux = function
    | [] -> l (* this is what is left, we could error *)
    | p::ps ->
       match p l with
       | None -> aux ps
       | Some l -> self#parse l
    in
      aux parsers

  method usage (fmt : Format.formatter) () =
    Format.pp_open_tbox fmt ();
    Format.pp_set_tab fmt ();
    Format.fprintf fmt "option";
    for i = 1 to max_len - 3 do Format.fprintf fmt " "; done;
    Format.pp_set_tab fmt ();
    Format.fprintf fmt "description";
    Format.pp_print_tab fmt ();
    List.iter (fun p -> p fmt ()) printers;
    Format.pp_close_tbox fmt ();
    Format.pp_print_newline fmt ()

end

(* convenient way of inheriting the API of a set of option *) 
class option_set (r : registry) = object
  method parse = r#parse
  method usage = r#usage
end

(* declaration of some options ------------------------------------------ *)

class         print_version = fun r -> object
  val mutable print_version = false 
       method print_version = print_version
  initializer r#register
    "-print-version" "prints the version of Coq"
    (Flag (fun () -> print_version <- true))
end

class         file_name = fun r -> object
  val mutable file_name = None
       method file_name = file_name
  initializer r#register
    "-file-name" "sets the file name of whatever"
    (String (fun x -> (* one could File.exists x here *) file_name <- Some x))
end

class         async_proofs = fun r -> object
  val mutable async_proofs = None
       method async_proofs = async_proofs
  initializer r#register
    "-async-proofs" "enables/disables super powers and this is a terribly long line that wraps around to test the documentation layout"
    (Bool (fun x -> async_proofs <- Some x))
end

type diffs_t = On | Off | Removed
class         diffs = fun r -> object
  val mutable diffs = Off
       method diffs = diffs
  initializer r#register
    "-diffs" "highlight differences between proof steps"
    (Enum(["on",On;"off",Off;"removed",Removed], (fun x -> diffs <- x)))
end

(* usage example --------------------------------------------------------- *)

class coqdep_options r =
  object(self)
    inherit option_set r

    inherit file_name r
    inherit print_version r
end

let coqdep_options = new coqdep_options (new registry);;

Format.printf "coqdep usage:@\n%a@\n" coqdep_options#usage ();;

let rest = coqdep_options#parse ["-print-version";"-file-name";"foo"];;
assert(rest=[]);;

module Coqdep : sig

  (* various ways to express the list of supported options *)
  (* I use .. or # to let one pass a larger set of options, but
   * we can also be strict. See the last example for a concrete use case *)

  val main : < print_version : bool;
               file_name : string option;
               .. >
          -> unit

  (* or we can use the exact set of options if it has a name *)
  val main2 : #coqdep_options -> unit

end = struct
  
  let main options = 
    Format.printf "Coqdep receives options: %b %s@\n@\n"
      options#print_version
      (match options#file_name with Some x -> x | _ -> "unset");;

  let main2 = main

end
  ;;

Coqdep.main coqdep_options;;
Coqdep.main2 coqdep_options;;

(* usage example -------------------------------------------------------- *)

(* Stm as a component, I add print_version just to complicate the next
 * example *)
class stm_options r = object
    inherit option_set r

    inherit print_version r
    inherit async_proofs r
end

module Stm : sig

  val init : #async_proofs -> unit

end = struct let init _ = () end

let stm_options = new stm_options (new registry);;
ignore(stm_options#parse ["-async-proofs";"yes"]);;
Stm.init stm_options;;

(* usage example -------------------------------------------------------- *)
  (* here I mix and mach:
      - single options
      - options for a component
      - options for a tool *)
class coqtop_options r = object
    inherit option_set r

    inherit stm_options r (* we take all options of the stm component *)
    inherit diffs r (* plus this one *)
    inherit! coqdep_options r (* plus the ones supported by coqdep *)
    (* Last line gets a warning that print_version occurs twice, to silence
     * it one can use inherit! (in both cases it works, since multiple
     * inheritance works in OCaml) *)
end

let coqtop_options = new coqtop_options (new registry);;
Format.printf "coqtop usage:@\n%a@\n" coqtop_options#usage ();;

coqtop_options#parse ["-diffs";"removed"];;

module Coqtop : sig

  val main : coqtop_options -> unit

end = struct
 
  let main o =
     (* the Stm.init type accepts any large enough set of options,
      * so we can directy pass o *)
     Stm.init o;
     Format.printf "diffs are: %s@\n"
        (match o#diffs with Removed -> "rm" | On -> "ok" | Off -> "off");;

end;;

Coqtop.main coqtop_options;;

```

# Drawbacks

Objects are not the most well known feature of OCaml, in spite of their beauty.

# Alternatives

One could use nested records. This approach has less flexibility, since
records cannot overlap and subtyping is not available. 


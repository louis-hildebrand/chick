open Syntax
module Context = Map.Make (String)
module Syntax = Syntax

type context = tp Context.t

exception Type_error of string

(** Check whether the types [t1] and [t2] are equal. *)
let type_eq (t1 : tp) (t2 : tp) : bool =
  (* TODO: This needs to be strengthened to compare vectors properly.
           Be careful to disallow "partial" terms (i.e., those containing
           fix f.t) *)
  t1 = t2

(** Check that, in context [ctxt], [tm] has type [typ]. *)
let rec check (ctxt : context) (tm : chk_tm) (typ : tp) : unit =
  match (tm, typ) with
  | Lam (x, body), Pi (_, t1, t2) -> check (ctxt |> Context.add x t1) body t2
  | Fix (x, body), typ -> check (ctxt |> Context.add x typ) body typ
  | Num _, Nat -> ()
  | Sum xs, Nat -> List.iter (fun t -> check ctxt t Nat) xs
  | Syn s, typ ->
      if type_eq (synth ctxt s) typ then ()
      else raise (Type_error "synthesizable term produced wrong type")
  | Nil, Vec (Num 0) -> ()
  (* TODO: need to check cons and match too *)
  | _ -> raise (Type_error "checkable term does not have expected type")

(** Synthesize a type from the term [t] in context [ctxt]. *)
and synth (ctxt : context) (t : syn_tm) : tp =
  match t with
  | Var x -> (
      match Context.find_opt x ctxt with
      | Some typ -> typ
      | None -> raise (Type_error "free variable"))
  | App (s, t) -> (
      match synth ctxt s with
      | Pi (_, t1, t2) ->
          (* TODO: should the context be extended here? *)
          check ctxt t t1;
          t2
      | _ ->
          raise (Type_error "left-hand side of application is not a function"))
  | Head (_, _) -> failwith "TODO"
  | Tail (_, _) -> failwith "TODO"

(** Typecheck a complete program. *)
let check_program (prog : program) : unit =
  let rec f (ctxt : context) (decls : program) : unit =
    match decls with
    | [] -> ()
    | d :: ds ->
        check ctxt d.body d.typ;
        f (ctxt |> Context.add d.name d.typ) ds
  in
  f Context.empty prog

open Domain
open Apron
open Abstract_syntax_tree
open Cfg

module type APRON_MANAGER =
sig
  type t
  val manager : t Manager.t
end

module OctagonManager : APRON_MANAGER =
struct
  type t = Oct.t
  let manager = Oct.manager_alloc ()
end

module PolyhedralManager : APRON_MANAGER =
struct
  type t = Polka.loose Polka.t
  let manager = Polka.manager_alloc_loose ()
end

module Make (M : APRON_MANAGER) : DOMAIN =
struct
  type t = M.t Abstract1.t

  let binop_to_tbinop op =
    let open Texpr1 in
    match op with
    | AST_PLUS -> Add
    | AST_MINUS -> Sub
    | AST_MULTIPLY -> Mul
    | AST_DIVIDE -> Div
    | AST_MODULO -> Mod

  let mpq_of_z t =
    Mpq.of_string (Z.to_string t)

  let var_to_tvar v =
    Apron.Var.of_string (v.var_name ^ "#" ^ (string_of_int v.var_id))

  let expr_to_texpr env e =
    let rec expr_to_texpr e =
      let open Texpr1 in
      match e with
      | CFG_int_unary (AST_UNARY_PLUS, e) -> expr_to_texpr e
      | CFG_int_unary (AST_UNARY_MINUS, e) -> Unop (Neg, expr_to_texpr e, Int, Zero)
      | CFG_int_binary (op, e1, e2) ->
	 Binop (binop_to_tbinop op, expr_to_texpr e1, expr_to_texpr e2, Int, Zero)
      | CFG_int_var v -> Var (var_to_tvar v)
      | CFG_int_const t ->
	 Cst (Coeff.s_of_mpq (mpq_of_z t))
      | CFG_int_rand (l, h) ->
	 Cst (Coeff.i_of_mpq (mpq_of_z l) (mpq_of_z h))
    in
    Texpr1.of_expr env (expr_to_texpr e)


  let init (vars : var list) : t =
    let vars =
      List.map var_to_tvar vars
      |> Array.of_list
    in
    let env = Environment.make vars [||] in
    Abstract1.of_box M.manager env vars
      (Array.make (Array.length vars) (Interval.of_int 0 0))

  let bottom_env env =
    Abstract1.bottom M.manager env

  let bottom vars =
    let vars =
      List.map var_to_tvar vars
      |> Array.of_list
    in
    Abstract1.bottom M.manager (Environment.make vars [||])

  let assign abstr var expr =
    Abstract1.assign_texpr M.manager abstr (var_to_tvar var)
      (expr_to_texpr (Abstract1.env abstr) expr) None

  let bwd_assign before v expr after =
    Abstract1.substitute_texpr
      M.manager after (var_to_tvar v)
      (expr_to_texpr (Abstract1.env before) expr) (Some before)

  let join = Abstract1.join M.manager

  let widen = Abstract1.widening M.manager

  let meet = Abstract1.meet M.manager

  let guard abstr expr =
    let binop op neg =
      match (op, neg) with
      | (AST_OR,  false) | (AST_AND, true) -> join
      | (AST_AND, false) | (AST_OR , true) -> meet
    in

    let compop env op neg =
      let constr0 typ e =
	let c = Tcons1.make e typ in
	let ar = Tcons1.array_make env 1 in
	Tcons1.array_set ar 0 c ;
	ar
      in
      let constr typ e1 e2 =
	let e =
	  expr_to_texpr env (CFG_int_binary (AST_MINUS, e1, e2))
	in
	constr0 typ e
      in


      let constr_rev typ e1 e2 = constr typ e2 e1 in
      match (op, neg) with
      | (AST_EQUAL, false) | (AST_NOT_EQUAL, true) -> constr Tcons1.EQ
      | (AST_NOT_EQUAL, false) | (AST_EQUAL, true) -> assert false
      | (AST_LESS, false) | (AST_GREATER_EQUAL, true) -> constr_rev Tcons1.SUP
      | (AST_LESS_EQUAL, false) | (AST_GREATER, true) -> constr_rev Tcons1.SUPEQ
      | (AST_GREATER, false) | (AST_LESS_EQUAL, true) -> constr Tcons1.SUP
      | (AST_GREATER_EQUAL, false) | (AST_LESS, true) -> constr Tcons1.SUPEQ
    in


    let rec impl abstr expr neg =
      match expr with
      | CFG_bool_unary (AST_NOT, e) ->
	 impl abstr e (not neg)
      | CFG_bool_binary (op, e1, e2) ->
	 (binop op neg) (impl abstr e1 neg) (impl abstr e2 neg)
      | CFG_compare (op, e1, e2) when ((op = AST_NOT_EQUAL && not neg)
				       || (op = AST_EQUAL && neg)) ->
	 impl abstr (CFG_bool_binary
		       (AST_OR,
			CFG_compare (AST_LESS, e1, e2),
			CFG_compare (AST_GREATER, e1, e2))) false
      | CFG_compare (op, e1, e2) ->
	 let cop = compop (Abstract1.env abstr) op neg in
	 Abstract1.meet_tcons_array M.manager abstr (cop e1 e2)
      | CFG_bool_const b ->
	 if b
	 then abstr
	 else bottom_env (Abstract1.env abstr)
      | CFG_bool_rand ->
	 abstr
    in
    impl abstr expr false

  let subset = Abstract1.is_leq M.manager

  let is_bottom = Abstract1.is_bottom M.manager

  let print oc d =
    Abstract1.print (Format.formatter_of_out_channel oc) d ;
    Printf.fprintf oc "\n"

end

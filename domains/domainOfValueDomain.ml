open Domain
open Value_domain
open Abstract_syntax_tree
open Cfg

module Make (V : VALUE_DOMAIN) : DOMAIN =
struct
  type t = V.t VarMap.t

  let init vars =
    List.fold_left (fun s x -> VarMap.add x (V.const Z.zero) s) VarMap.empty vars

  let bottom _ = VarMap.empty

  let filter_empty vars =
    if VarMap.exists (fun _ x -> (V.is_bottom x)) vars
    then bottom []
    else vars

  let meet a b =
    VarMap.map2o (fun _ _ -> V.bottom) (fun _ _ -> V.bottom) (fun _ -> V.meet) a b
    |> filter_empty

  let join =
    let id x = x in
    VarMap.map2o (fun _ -> id) (fun _ -> id) (fun _ -> V.join)

  let eval_var vars var =
    try VarMap.find var vars
    with Not_found -> V.bottom

  let assign vars var expr =
    let rec evaluate expr =
      match expr with
      | CFG_int_unary (op, e) ->
	 V.unary (evaluate e) op
      | CFG_int_binary (op, e1, e2) ->
	 V.binary (evaluate e1) (evaluate e2) op
      | CFG_int_var v ->
	 eval_var vars v
      | CFG_int_const c ->
	 V.const c
      | CFG_int_rand (a, b) ->
	 V.rand a b
    in
    VarMap.add var (evaluate expr) vars
    |> filter_empty


  module EvalutionTree =
  struct
    type u =
      | Variable of Var.t
      | Const
      | UnaryOp of int_unary_op * t
      | BinaryOp of int_binary_op * t * t
    and t =
      {
	domain: V.t ;
	underlying: u
      }


    let rec eval vars expr =
      match expr with
      | CFG_int_unary (op, e) ->
	 let v = eval vars e in
	 {
	   domain = V.unary v.domain op ;
	   underlying = UnaryOp (op, v)
	 }
      | CFG_int_binary (op, e1, e2) ->
	 let v1 = eval vars e1 in
	 let v2 = eval vars e2 in
	 {
	   domain = V.binary v1.domain v2.domain op ;
	   underlying = BinaryOp (op, v1, v2)
	 }
      | CFG_int_var v ->
	 {
	   domain = eval_var vars v ;
	   underlying = Variable v
	 }
      | CFG_int_const c ->
	 {
	   domain = V.const c ;
	   underlying = Const
	 }
      | CFG_int_rand (a, b) ->
	 {
	   domain = V.rand a b ;
	   underlying = Const
	 }

    let rec bwd_eval vars tree dom =
      match tree.underlying with
      | Variable v ->
	 VarMap.add v (V.meet tree.domain dom) vars
      | Const ->
	 if V.is_bottom (V.meet dom tree.domain)
	 then bottom []
	 else vars
      | UnaryOp (op, e) ->
	 let edom = V.bwd_unary e.domain op dom in
	 bwd_eval vars e edom
      | BinaryOp (op, e1, e2) ->
	 let (e1dom, e2dom) = V.bwd_binary e1.domain e2.domain op dom in
	 meet (bwd_eval vars e1 e1dom) (bwd_eval vars e2 e2dom)
  end
  let bwd_assign vars v expr after =
    let open EvalutionTree in
    bwd_eval (VarMap.add v (eval_var vars v) after)
      (eval vars expr) (eval_var after v)


  let guard vars expr =
    let binop op neg =
      match (op, neg) with
      | (AST_OR,  false) | (AST_AND, true) -> join
      | (AST_AND, false) | (AST_OR , true) -> meet
    in

    let compop op neg =
      match (op, neg) with
      | (AST_EQUAL, false) | (AST_NOT_EQUAL, true) -> AST_EQUAL
      | (AST_NOT_EQUAL, false) | (AST_EQUAL, true) -> AST_NOT_EQUAL
      | (AST_LESS, false) | (AST_GREATER_EQUAL, true) -> AST_LESS
      | (AST_LESS_EQUAL, false) | (AST_GREATER, true) -> AST_LESS_EQUAL
      | (AST_GREATER, false) | (AST_LESS_EQUAL, true) -> AST_GREATER
      | (AST_GREATER_EQUAL, false) | (AST_LESS, true) -> AST_GREATER_EQUAL
    in

    let rec impl vars expr neg =
      match expr with
      | CFG_bool_unary (AST_NOT, e) ->
	 impl vars e (not neg)
      | CFG_bool_binary (op, e1, e2) ->
	 (binop op neg) (impl vars e1 neg) (impl vars e2 neg)
      | CFG_compare (op, e1, e2) ->
	 let open EvalutionTree in
	 let cop = compop op neg in
	 let t1 = eval vars e1 in
	 let t2 = eval vars e2 in
	 let (d1, d2) = V.compare t1.domain t2.domain cop in
	 meet (bwd_eval vars t1 d1) (bwd_eval vars t2 d2)
      | CFG_bool_const b ->
	 if b then vars else bottom []
      | CFG_bool_rand ->
	 vars
    in
    impl vars expr false


  let widen a b =
    let id x = x in
    VarMap.map2o (fun _ -> id) (fun _ -> id)
      (fun _ -> V.widen) a b

  let subset =
    VarMap.for_all2o
      (fun _ -> V.is_bottom) (fun _ _ -> true)
      (fun _ -> V.subset)

  let is_bottom =
    VarMap.equal (=) (bottom [])




  let print out =
    let print_pos (pos, _) =
      Printf.sprintf "@%s, l%d" pos.Lexing.pos_fname pos.Lexing.pos_lnum
    in
    let print_var v =
      Printf.sprintf "%s [%s]" v.var_name (print_pos v.var_pos)
    in
    VarMap.iter (fun key value ->
      output_string out (print_var key) ;
      output_string out " -> " ;
      V.print out value ;
      output_string out "\n"
    )


end

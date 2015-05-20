open Domain
open Cfg

type incoming_flow =
  | Arc of arc
  | FunctionCall of node * func
  | FunctionExit of node * func



module Make (D : DOMAIN) =
struct


  exception FailingTrace of (D.t * (incoming_flow list))



  type t =
    {
      worklist : node list ;
      invariants : D.t NodeMap.t ;
      entry_points : func NodeMap.t ;
      exit_points : func NodeMap.t ;
      cfg : cfg
    }

  let evaluate_instr dvalue invariants arc =
    let res = NodeMap.find arc.arc_dst invariants in
    match arc.arc_inst with
    | CFG_skip _ -> D.meet dvalue res
    | CFG_assign (var, expr) -> D.bwd_assign dvalue var expr res
    | CFG_guard expr -> D.guard (D.meet dvalue res) expr
    | CFG_assert expr -> D.meet dvalue res
    | CFG_call f -> NodeMap.find f.func_entry invariants

  let predecessors entry_points node wl =
    let wl =
      try
	let f = NodeMap.find node entry_points in
	List.fold_left (fun wl a -> a.arc_src :: wl) wl f.func_calls
      with Not_found -> wl
    in
    List.fold_left (fun wl arc ->
      (match arc.arc_inst with
      | CFG_call f -> f.func_exit
      | _ -> arc.arc_src) :: wl) wl node.node_in

  let call_to invariants exit_points node dvalues =
    try
      let f = NodeMap.find node exit_points in
      List.fold_left (fun dvalues a ->
	NodeMap.find a.arc_dst invariants :: dvalues
      ) dvalues f.func_calls
    with Not_found -> dvalues

  let examine_regular iter node worklist cont =
    let arcs = node.node_out in
    let old_dvalue = NodeMap.find node iter.invariants in
    let dvalue =
      arcs
      |> List.map (evaluate_instr old_dvalue iter.invariants)
      |> call_to iter.invariants iter.exit_points node
      |> List.fold_left D.join (D.bottom iter.cfg.cfg_vars)
    in
    if D.subset old_dvalue dvalue
    then cont { iter with worklist }
    else
      let worklist = predecessors iter.entry_points node worklist in
      let invariants = NodeMap.add node dvalue iter.invariants in
      cont { iter with worklist ; invariants }


  let rec examine_next iter =
    match iter.worklist with
    | [] -> iter.invariants
    | node :: worklist -> examine_regular iter node worklist examine_next


  let rec find_main funcs =
    match funcs with
    | [] ->
       begin
	 Printf.eprintf "ERR : Main not found\n" ;
	 failwith "No main found !"
       end
    | f :: funcs ->
       if f.func_name = "main"
       then f
       else find_main funcs

  let print_widening_points wpoints =
    Printf.printf "Widening points set at :\n" ;
    NodeSet.iter (fun node ->
      Printf.printf "Node %d (%s, l%d)\n"
	node.node_id
	node.node_pos.Lexing.pos_fname
	node.node_pos.Lexing.pos_lnum
    ) wpoints


  let print_invariants =
    NodeMap.iter (fun node dval ->
      Printf.printf "\nNode %d (%s, l%d) : \n"
	node.node_id
	node.node_pos.Lexing.pos_fname
	node.node_pos.Lexing.pos_lnum ;
      D.print stdout dval)

  let mark_widening_points cfg =
    List.fold_left (fun pts arc ->
      let pos_src = arc.arc_src.node_pos in
      let pos_dst = arc.arc_dst.node_pos in
      if pos_src.Lexing.pos_cnum <= pos_dst.Lexing.pos_cnum
      then pts
      else NodeSet.add arc.arc_dst pts
    ) NodeSet.empty cfg.cfg_arcs


  let rec find_failing_trace acc invariants visited entry_points exit_points src dst =
    let incoming node =
      let incoming =
	try
	  let f = NodeMap.find node entry_points in
	  List.fold_left
	    (fun i a -> FunctionCall (a.arc_src, f)  :: i)
	    [] f.func_calls
	with Not_found -> []
    in
      List.fold_left (fun i arc ->
	(match arc.arc_inst with
	| CFG_call f -> FunctionExit (arc.arc_dst, f)
	| _ -> Arc arc) :: i) incoming node.node_in
    in

    let source fl =
      match fl with
      | Arc a -> a.arc_src
      | FunctionCall (src, _) -> src
      | FunctionExit (_, f) -> f.func_exit
    in

    let visited = NodeSet.add dst visited in
    if src.node_id = dst.node_id
    then raise (FailingTrace (NodeMap.find src invariants, acc))
    else
      List.iter (fun f ->
	let n = source f in
	if not (NodeSet.mem n visited)
	  && not (D.is_bottom (NodeMap.find n invariants))
	then find_failing_trace (f :: acc) invariants visited entry_points exit_points src n
      ) (incoming dst)

  let iterate cfg initial_invariants (node, expr) =

    let main_func = find_main cfg.cfg_funcs in

    let entry_points =
      List.fold_left (fun ent f -> NodeMap.add f.func_entry f ent)
	NodeMap.empty cfg.cfg_funcs
    in

    let exit_points =
      List.fold_left (fun ent f -> NodeMap.add f.func_exit f ent)
	NodeMap.empty cfg.cfg_funcs
    in


    let iter =
      {
	worklist = predecessors entry_points node [] ;
	invariants =
	  NodeMap.add node
	    (D.guard
	       (NodeMap.find node initial_invariants)
	       (CFG_bool_unary (Abstract_syntax_tree.AST_NOT, expr)))
	    initial_invariants ;
	entry_points ;
	exit_points ;
	cfg
      }
    in
    let invariants = examine_next iter in

    let trace =
      try
	begin
	  find_failing_trace [] invariants NodeSet.empty
	    entry_points exit_points
	    main_func.func_entry node ;
	  None
	end
      with FailingTrace tr -> Some tr
    in
    (invariants, trace)

end

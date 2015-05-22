open Domain
open Cfg



module Make (D : DOMAIN) =
struct


  exception FailingTrace of (D.t * (arc list))

  type t =
    {
      worklist : node list ;
      invariants : D.t NodeMap.t ;
      cfg : cfg
    }

  let evaluate_instr dvalue invariants arc =
    let res = NodeMap.find arc.arc_dst invariants in
    match arc.arc_inst with
    | CFG_skip _ -> D.meet dvalue res
    | CFG_assign (var, expr) -> D.bwd_assign dvalue var expr res
    | CFG_guard expr -> D.guard (D.meet dvalue res) expr
    | CFG_assert expr -> D.meet dvalue res
    | CFG_call f -> assert false

  let predecessors node wl =
    List.fold_left (fun wl arc ->
      (match arc.arc_inst with
      | CFG_call f -> assert false
      | _ -> arc.arc_src) :: wl) wl node.node_in

  let examine_regular iter node worklist cont =
    let arcs = node.node_out in
    let old_dvalue = NodeMap.find node iter.invariants in
    let dvalue =
      arcs
      |> List.map (evaluate_instr old_dvalue iter.invariants)
      |> List.fold_left D.join (D.bottom iter.cfg.cfg_vars)
    in
    if D.subset old_dvalue dvalue
    then cont { iter with worklist }
    else
      let worklist = predecessors node worklist in
      let invariants = NodeMap.add node dvalue iter.invariants in
      cont { iter with worklist ; invariants }


  let rec examine_next iter =
    match iter.worklist with
    | [] -> iter.invariants
    | node :: worklist -> examine_regular iter node worklist examine_next


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


  let rec find_failing_trace acc invariants visited src dst =
    let incoming node = node.node_in in
    let source fl = fl.arc_src in

    let visited = NodeSet.add dst visited in
    if src.node_id = dst.node_id
    then raise (FailingTrace (NodeMap.find src invariants, acc))
    else
      List.iter (fun f ->
	let n = source f in
	if not (NodeSet.mem n visited)
	  && not (D.is_bottom (NodeMap.find n invariants))
	then find_failing_trace (f :: acc) invariants visited src n
      ) (incoming dst)

  let iterate cfg initial_invariants (node, expr) =

    let iter =
      {
	worklist = predecessors node [] ;
	invariants =
	  NodeMap.add node
	    (D.guard
	       (NodeMap.find node initial_invariants)
	       (CFG_bool_unary (Abstract_syntax_tree.AST_NOT, expr)))
	    initial_invariants ;
	cfg
      }
    in
    let invariants = examine_next iter in

    let trace =
      try
	begin
	  find_failing_trace [] invariants NodeSet.empty
	    cfg.cfg_init_entry node ;
	  None
	end
      with FailingTrace tr -> Some tr
    in
    (invariants, trace)

end

open Domain
open Cfg

module Make (D : DOMAIN) =
struct
  type t =
    {
      worklist : node list ;
      invariants : D.t NodeMap.t ;
      (*initial_invariants : D.t NodeMap.t ; *)
      widening_points : NodeSet.t ;
      dec_iterations : int NodeMap.t ;
      max_dec_iterations : int ;
      entry_points : func NodeMap.t ;
      exit_points : func NodeMap.t ;
      cfg : cfg
    }

  let bwd_invariants vars invariants n =
    try NodeMap.find n invariants
    with Not_found -> D.bottom vars

  let evaluate_instr vars dvalue invariants arc =
    let res = bwd_invariants vars invariants arc.arc_dst in
    let a =
      match arc.arc_inst with
      | CFG_skip _ -> D.meet dvalue res
      | CFG_assign (var, expr) -> D.bwd_assign dvalue var expr res
      | CFG_guard expr -> D.guard (D.meet dvalue res) expr
      | CFG_assert expr -> D.meet dvalue res
      (*D.guard (D.meet dvalue res) expr *)
      | CFG_call f ->
	 bwd_invariants vars invariants f.func_entry
    in
    Printf.printf "Node %d <- %d:\n" arc.arc_dst.node_id arc.arc_src.node_id ;
    D.print stdout a ;
    Printf.printf "\n" ;
    a

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

  let call_to vars invariants exit_points node dvalues =
    try
      let f = NodeMap.find node exit_points in
      List.fold_left (fun dvalues a ->
	bwd_invariants vars invariants a.arc_dst :: dvalues
      ) dvalues f.func_calls
    with Not_found -> dvalues

  let examine_regular iter node worklist cont =
    Printf.printf "Examinde node %d...\n" node.node_id ;
    let arcs = node.node_out in
    let dvalue =
    (*  try *) NodeMap.find node iter.invariants
    (*      with Not_found -> NodeMap.find node iter.initial_invariants *)
    in
    let dvalue =
      arcs
      |> List.map (evaluate_instr iter.cfg.cfg_vars dvalue iter.invariants)
      |> call_to iter.cfg.cfg_vars iter.invariants iter.exit_points node
      |> List.fold_left D.join (D.bottom iter.cfg.cfg_vars)
    in
    if D.subset (bwd_invariants iter.cfg.cfg_vars iter.invariants node) dvalue
    then cont { iter with worklist }
    else
      let worklist = predecessors iter.entry_points node worklist in
      let invariants = NodeMap.add node dvalue iter.invariants in
      cont { iter with worklist ; invariants }

  let examine_widening_point iter node worklist cont =
    let arcs = node.node_out in
    let dvalue =
    (*  try *) NodeMap.find node iter.invariants
    (*      with Not_found -> NodeMap.find node iter.initial_invariants *)
    in
    let dvalue =
      arcs
      |> List.map (evaluate_instr iter.cfg.cfg_vars dvalue iter.invariants)
      |> call_to iter.cfg.cfg_vars iter.invariants iter.exit_points node
      |> List.fold_left D.join (D.bottom iter.cfg.cfg_vars)
    in
    let old_dvalue = bwd_invariants iter.cfg.cfg_vars iter.invariants node in
    let wdvalue = D.widen old_dvalue dvalue in
    if D.subset wdvalue old_dvalue
    then
      begin
	let dec_it =
	  try NodeMap.find node iter.dec_iterations
	  with Not_found -> 0
	in
	if dec_it < iter.max_dec_iterations
	then
	  let dec_iterations = NodeMap.add node (succ dec_it) iter.dec_iterations in
	  let worklist = predecessors iter.entry_points node worklist in
	  let invariants = NodeMap.add node dvalue iter.invariants in
	  Printf.printf "Temporary value at iteration %d:\n" (succ dec_it) ;
	  D.print stdout dvalue ;
	  cont { iter with worklist ; invariants ; dec_iterations }
	else cont { iter with worklist }
      end
    else
      begin
	let dec_iterations = NodeMap.add node 0 iter.dec_iterations in
	let worklist = predecessors iter.entry_points node worklist in
	let invariants = NodeMap.add node wdvalue iter.invariants in
	cont { iter with worklist ; invariants ; dec_iterations }

      end


  let rec examine_next iter =
    match iter.worklist with
    | [] -> iter.invariants
    | node :: worklist ->
       (*if NodeSet.mem node iter.widening_points
       then examine_widening_point iter node worklist examine_next
	 else*) examine_regular iter node worklist examine_next


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

  let rec find_failing_trace oc invariants visited src dst =
    let visited = NodeSet.add dst visited in
    (*    Printf.printf "Visiting node %d...\n" dst.node_id ; *)
    if src.node_id = dst.node_id
    then (
      Printf.printf " found failing trace!\n" ;
      Printf.printf "Entering main with values :\n" ;
      D.print oc (NodeMap.find src invariants) ;
      Printf.printf "Then :\n" ;
      true)
    else
      List.exists (fun a ->
	let n = a.arc_src in
	(*	Printf.printf "  checking node %d...\n" n.node_id ; *)
	try
	  if not (NodeSet.mem n visited)
	    && not (D.is_bottom (NodeMap.find n invariants))
	    && find_failing_trace oc invariants visited src n
	  then
	    begin
	      Printf.fprintf oc "  %i -> %i: %a\n"
		a.arc_src.node_id a.arc_dst.node_id Cfg_printer.print_inst a.arc_inst ;
	      true
	    end
	  else false
	with _ -> false
      ) dst.node_in

  let iterate cfg initial_invariants (node, expr) =

    let widening_points = mark_widening_points cfg in
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
	dec_iterations = NodeMap.empty ;
	max_dec_iterations = 5 ;
	widening_points ;
	entry_points ;
	exit_points ;
	cfg
      }
    in
    let invariants = examine_next iter in

    Printf.printf "\n\nMain function, backward:\n" ;
    print_invariants invariants ;

    Printf.printf "Assertion on %a failed on foward analysis.\n"
      Cfg_printer.print_bool_expr expr ;
    Printf.printf "Searching a trace of failure... " ;
    if not (find_failing_trace stdout invariants
	      NodeSet.empty main_func.func_entry node)
    then Printf.printf "  false alarm.\n"

end

open Domain
open Cfg

module Make (D : DOMAIN) =
struct
  type t =
    {
      worklist : node list ;
      invariants : D.t NodeMap.t ;
      widening_points : NodeSet.t ;
      dec_iterations : int NodeMap.t ;
      max_dec_iterations : int ;
      entry_points : func NodeMap.t ;
      exit_points : func NodeMap.t ;
      cfg : cfg ;
      skip_assert : bool
    }


  let evaluate_instr skip_assert invariants arc =
    let dvalue = NodeMap.find arc.arc_src invariants in
    match arc.arc_inst with
    | CFG_skip _ -> dvalue
    | CFG_assign (var, expr) -> D.assign dvalue var expr
    | CFG_guard expr -> D.guard dvalue expr
    | CFG_assert expr ->
       if skip_assert
       then dvalue
       else D.guard dvalue expr
    | CFG_call f ->
       NodeMap.find f.func_exit invariants


  let successors exit_points node wl =
    let wl =
      try
	let f = NodeMap.find node exit_points in
	List.fold_left (fun wl a -> a.arc_dst :: wl) wl f.func_calls
      with Not_found -> wl
    in
    List.fold_left (fun wl arc ->
      (match arc.arc_inst with
      | CFG_call f -> f.func_entry
      | _ -> arc.arc_dst) :: wl) wl node.node_out

  let call_in invariants entry_points node dvalues =
    try
      let f = NodeMap.find node entry_points in
      List.fold_left (fun dvalues a ->
	NodeMap.find a.arc_src invariants :: dvalues
      ) dvalues f.func_calls
    with Not_found -> dvalues

  let examine_regular iter node worklist cont =
    let arcs = node.node_in in
    let dvalue =
      arcs
    |> List.map (evaluate_instr iter.skip_assert iter.invariants)
    |> call_in iter.invariants iter.entry_points node
    |> List.fold_left D.join (D.bottom iter.cfg.cfg_vars)
    in
    if D.subset dvalue (NodeMap.find node iter.invariants)
    then cont { iter with worklist }
    else
      let worklist = successors iter.exit_points node worklist in
      let invariants = NodeMap.add node dvalue iter.invariants in
      cont { iter with worklist ; invariants }

  let examine_widening_point iter node worklist cont =
    let arcs = node.node_in in
    let dvalue =
      arcs
      |> List.map (evaluate_instr iter.skip_assert iter.invariants)
      |> call_in iter.invariants iter.entry_points node
      |> List.fold_left D.join (D.bottom iter.cfg.cfg_vars)
    in
    let old_dvalue = NodeMap.find node iter.invariants in
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
	  let worklist = successors iter.exit_points node worklist in
	  let invariants = NodeMap.add node dvalue iter.invariants in
	  cont { iter with worklist ; invariants ; dec_iterations }
	else cont { iter with worklist }
      end
    else
      begin
	let dec_iterations = NodeMap.add node 0 iter.dec_iterations in
	let worklist = successors iter.exit_points node worklist in
	let invariants = NodeMap.add node wdvalue iter.invariants in
	cont { iter with worklist ; invariants ; dec_iterations }

      end


  let rec examine_next iter =
    match iter.worklist with
    | [] -> iter.invariants
    | node :: worklist ->
       if NodeSet.mem node iter.widening_points
       then examine_widening_point iter node worklist examine_next
       else examine_regular iter node worklist examine_next




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




  let print_assertion_failed oc arcs invariants =
    List.iter (fun a ->
      match a.arc_inst with
      | CFG_assert expr ->
	 let dsrc = NodeMap.find a.arc_src invariants in
	 let dfailed =
	   D.guard
	     dsrc (CFG_bool_unary (Abstract_syntax_tree.AST_NOT, expr))
	 in
	 if not (D.is_bottom dfailed)
	 then
	   Printf.fprintf oc " Assertion  %i -> %i: %a failed\n"
	     a.arc_src.node_id a.arc_dst.node_id Cfg_printer.print_inst a.arc_inst
      | _ -> ()
    ) arcs


  let assertion_failed arcs invariants =
    List.fold_left (fun acc a ->
      match a.arc_inst with
      | CFG_assert expr ->
	 let dsrc = NodeMap.find a.arc_src invariants in
	 let dfailed =
	   D.guard
	     dsrc (CFG_bool_unary (Abstract_syntax_tree.AST_NOT, expr))
	 in
	 if not (D.is_bottom dfailed)
	 then (a.arc_src, expr) :: acc
	 else acc
      | _ -> acc
    ) [] arcs

  let mark_widening_points cfg =
    List.fold_left (fun pts arc ->
      let pos_src = arc.arc_src.node_pos in
      let pos_dst = arc.arc_dst.node_pos in
      if pos_src.Lexing.pos_cnum <= pos_dst.Lexing.pos_cnum
      then pts
      else NodeSet.add arc.arc_dst pts
    ) NodeSet.empty cfg.cfg_arcs


  let iterate cfg skip_assert =
    let widening_points = mark_widening_points cfg in

    let entry_points =
      List.fold_left (fun ent f -> NodeMap.add f.func_entry f ent) NodeMap.empty cfg.cfg_funcs
    in

    let exit_points =
      List.fold_left (fun ent f -> NodeMap.add f.func_exit f ent) NodeMap.empty cfg.cfg_funcs
    in



    (*    print_widening_points widening_points ; *)

    let iter =
      {
	worklist = successors exit_points cfg.cfg_init_entry [] ;
	invariants =
	  List.fold_left (fun inv node -> NodeMap.add node (D.bottom cfg.cfg_vars) inv) NodeMap.empty cfg.cfg_nodes
	  |> NodeMap.add cfg.cfg_init_entry (D.init cfg.cfg_vars) ;
	widening_points ;
	entry_points ;
	exit_points ;
	dec_iterations = NodeMap.empty ;
	max_dec_iterations = 3 ;
	skip_assert ;
	cfg
      }
    in
    let invariants = examine_next iter in

    let main_func = find_main cfg.cfg_funcs in

    let iter =
      {
	worklist = successors exit_points main_func.func_entry [] ;
	invariants =
	  invariants
	  |> NodeMap.add main_func.func_entry (NodeMap.find cfg.cfg_init_exit invariants) ;
	dec_iterations = NodeMap.empty ;
	entry_points ;
	exit_points ;
	max_dec_iterations = 3 ;
	widening_points ;
	skip_assert ;
	cfg
      }
    in
    let invariants = examine_next iter in
    (invariants, assertion_failed cfg.cfg_arcs invariants)

end

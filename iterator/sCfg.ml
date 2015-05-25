open Cfg

let add_incoming nd arc =
  nd.node_in <- arc :: nd.node_in

let add_outgoing nd arc =
  nd.node_out <- arc :: nd.node_out

let add_startup cfg (arcs, id) =
  let main =
    List.find (fun f -> f.func_name = "main") cfg.cfg_funcs
  in	
  let (enter_main, id) =
    ({ arc_id = id ;
       arc_src = cfg.cfg_init_exit ;
       arc_dst = main.func_entry ;
       arc_inst = CFG_skip ("Enter main") },
     succ id)
  in
  let arcs = enter_main :: arcs in  
  add_incoming enter_main.arc_dst enter_main ;
  add_outgoing enter_main.arc_src enter_main ;
  (arcs, id)

        
let of_cfg cfg =
  let max_id =
    List.map (fun a -> a.arc_id) cfg.cfg_arcs
    |> List.fold_left max 0
    |> (+) 1
  in
  List.iter (fun n -> n.node_in <- [] ; n.node_out <- []) cfg.cfg_nodes ;
  
  let (arcs, id) =
    List.fold_left (fun (arcs, id) a ->
      match a.arc_inst with
      | CFG_call f ->
	 let (enter_f, id) =
	   ({ arc_id = id ;
	      arc_src = a.arc_src ;
	      arc_dst = f.func_entry ;
	      arc_inst = CFG_skip ("Enter function " ^ f.func_name) },
	    succ id)
	 in
	 let (exit_f, id) =
	   ({ arc_id = id ;
	      arc_src = f.func_exit ;
	      arc_dst = a.arc_dst ;
	      arc_inst = CFG_skip ("Exit function " ^ f.func_name) },
	   succ id)
	 in
	 let arcs = enter_f :: exit_f :: arcs in
	 add_incoming enter_f.arc_dst enter_f ;
	 add_incoming exit_f.arc_dst exit_f ;
	 add_outgoing enter_f.arc_src enter_f ;
	 add_outgoing exit_f.arc_src exit_f ;
	 (arcs, id)
      | _ ->
	 let arcs = a :: arcs in
	 add_incoming a.arc_dst a ;
	 add_outgoing a.arc_src a ;
	 (arcs, id)
    ) ([], max_id) cfg.cfg_arcs
    |> add_startup cfg
  in
  
  {
    cfg_vars = cfg.cfg_vars ;
    cfg_funcs = cfg.cfg_funcs ;
    cfg_nodes = cfg.cfg_nodes ;
    cfg_arcs = arcs ;
    cfg_init_entry = cfg.cfg_init_entry ;
    cfg_init_exit = cfg.cfg_init_exit
  }

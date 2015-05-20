open Value_domain
open Constant
open Interval
open Domain
(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Antoine Miné 2015
  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(*
  Simple driver: parses the file given as argument and prints it back.

  You should modify this file to call your functions instead!
*)

module Constant = DomainOfValueDomain.Make(ConstantValueDomain)
module Interval = DomainOfValueDomain.Make(IntervalValueDomain)
module Octagon = ApronDomain.Make(ApronDomain.OctagonManager)
module Polyhedra = ApronDomain.Make(ApronDomain.PolyhedralManager)







(* parse filename *)
let doit domain backward_analysis false_alarms filename =
  let module Dom = (val domain : DOMAIN) in
  let module Iterator = Forward.Make(Dom) in
  let module BackwardIterator = Backward.Make(Dom) in


  let print_failing_trace oc (src_inv, tr) =
    Printf.fprintf oc "Entering main with values :\n" ;
    Dom.print oc src_inv ;
    Printf.printf "Then :\n" ;
    List.iter (fun fl ->
      let open Backward in
      let open Cfg in
      match fl with
      | Arc a ->
	 Printf.fprintf oc "  %i -> %i: %a\n"
	   a.arc_src.node_id a.arc_dst.node_id Cfg_printer.print_inst a.arc_inst ;
      | FunctionCall (call_site, f) ->
	 Printf.fprintf oc "  %i -> %i: Entering function %s\n"
	   call_site.node_id f.func_entry.node_id f.func_name
      | FunctionExit (exit_site, f) ->
	 Printf.fprintf oc "  %i -> %i: Entering function %s\n"
	  f.func_exit.node_id  exit_site.node_id  f.func_name
      ) tr
  in

  let prog = File_parser.parse_file filename in

  let cfg = Tree_to_cfg.prog prog in
  Printf.printf "%a\n" Cfg_printer.print_cfg cfg;
  let (invariants, failed_assertions) = Iterator.iterate cfg in
  if backward_analysis
  then
    List.iter (fun fa ->
      let (invariants, tr) = BackwardIterator.iterate cfg invariants fa in
      match tr with
      | Some ft ->
	 begin
	   Printf.printf "Assertion on %a failed on foward analysis.\n"
	     Cfg_printer.print_bool_expr (snd fa) ;
	   Printf.printf "Searching a trace of failure... found a failing trace!" ;
	   print_failing_trace stdout ft
	 end
      | None when false_alarms ->
	 begin
	   Printf.printf "Assertion on %a failed on foward analysis.\n"
	     Cfg_printer.print_bool_expr (snd fa) ;
	   Printf.printf "Searching a trace of failure... false alarm"
	 end
      | None -> ()

    ) failed_assertions
  else
    List.iter (fun (x, expr) ->
      Printf.printf "Assertion %a failed.\n"
	Cfg_printer.print_bool_expr expr
    ) failed_assertions ;

  Cfg_printer.output_dot "cfg.dot" cfg



let domains =
  [ "constant"  , (module Constant  : DOMAIN) ;
    "interval"  , (module Interval  : DOMAIN) ;
    "octagon"   , (module Octagon   : DOMAIN) ;
    "polyhedra" , (module Polyhedra : DOMAIN)]

let domains_name = List.split domains |> fst
let set_domain dom s = dom := List.assoc s domains

(* parses arguments to get filename *)
let main () =
  let domain = ref (module Interval : DOMAIN) in
  let backward_analysis = ref true in
  let false_alarms = ref true in
  let filename = ref None in
  Arg.(parse
    [ "-domain", Symbol (domains_name, set_domain domain), "Abstract domain" ;
      "-backward-analysis"   , Set   backward_analysis, "Perform backward analysis" ;
      "-no-backward-analysis", Clear backward_analysis, "Don't perform backward analysis" ;
      "-false-alarms"   , Set   false_alarms, "Print false alarms" ;
      "-no-false-alarms", Clear false_alarms, "Don't print false alarms" ]
    (fun s -> filename := Some s)
    "");
  match !filename with
  | Some filename ->
     doit !domain !backward_analysis !false_alarms filename
  | None -> invalid_arg "No source file specified"

let _ =
  try main ()
  with Apron.Manager.Error e -> Apron.Manager.print_exclog Format.std_formatter e

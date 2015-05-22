open Value_domain
open Abstract_syntax_tree

module IntervalValueDomain : VALUE_DOMAIN =
struct
  module Bounds =
  struct
    type t =
      | MinusInfinite
      | Finite of Z.t
      | Infinite

    let (<=?) a b =
      match (a, b) with
      | (MinusInfinite, _) -> true
      | (Finite na, Finite nb) -> Z.leq na nb
      | (_, Infinite) -> true
      | _ -> false

    let (>=?) a b = b <=? a
    let (<?) a b = not (a >=? b)
    let (>?) a b = not (a <=? b)

    let (~?) = function
      | MinusInfinite -> Infinite
      | Finite n -> Finite (Z.neg n)
      | Infinite -> MinusInfinite

    let (+?) a b =
      match (a, b) with
      | (MinusInfinite, Infinite)
      | (Infinite, MinusInfinite) -> failwith "Could not add opposite infinite"
      | (MinusInfinite, _)
      | (_, MinusInfinite) -> MinusInfinite
      | (Infinite, _)
      | (_, Infinite) -> Infinite
      | (Finite na, Finite nb) -> Finite (Z.add na nb)

    let ( *? ) a b =
      match (a, b) with
      | (MinusInfinite, Infinite)
      | (Infinite, MinusInfinite) -> MinusInfinite
      | (MinusInfinite, MinusInfinite)
      | (Infinite, Infinite) -> Infinite
      | (MinusInfinite, Finite x)
      | (Finite x, MinusInfinite) ->
	 if Z.lt x Z.zero
	 then Infinite
	 else if Z.gt x Z.zero
	 then MinusInfinite
	 else Finite Z.zero
      | (Infinite, Finite x)
      | (Finite x, Infinite) ->
	 if Z.lt x Z.zero
	 then MinusInfinite
	 else if Z.gt x Z.zero
	 then Infinite
	 else Finite Z.zero
      | (Finite x, Finite y) ->
	 Finite (Z.mul x y)

    let mul = ( *? )

    let (/?) a b =
      match (a, b) with
      | (_, MinusInfinite) | (_, Infinite) -> Finite Z.zero
      | (MinusInfinite, Finite n) ->
	 if Z.lt n Z.zero
	 then Infinite
	 else if Z.gt n Z.zero
	 then MinusInfinite
	 else failwith "Division by 0"
      | (Infinite, Finite n) ->
	 if Z.lt n Z.zero
	 then MinusInfinite
	 else if Z.gt n Z.zero
	 then Infinite
	 else failwith "Division by 0"
      | (Finite num, Finite den) ->
	 Finite (Z.div num den)

    let div = (/?)

    let min a b =
      match (a, b) with
      | (MinusInfinite, _)
      | (_, MinusInfinite) -> MinusInfinite
      | (Finite na, Finite nb) -> Finite (Z.min na nb)
      | (Finite n, Infinite)
      | (Infinite, Finite n) -> Finite n
      | (Infinite, Infinite) -> Infinite

    let max a b =
      match (a, b) with
      | (Infinite, _)
      | (_, Infinite) -> Infinite
      | (Finite na, Finite nb) -> Finite (Z.max na nb)
      | (Finite n, MinusInfinite)
      | (MinusInfinite, Finite n) -> Finite n
      | (MinusInfinite, MinusInfinite) -> MinusInfinite

    let pred x =
      match x with
      | MinusInfinite -> MinusInfinite
      | Finite n -> Finite (Z.pred n)
      | Infinite -> Infinite

    let succ x =
      match x with
      | MinusInfinite -> MinusInfinite
      | Finite n -> Finite (Z.succ n)
      | Infinite -> Infinite

    let abs x =
      match x with
      | MinusInfinite | Infinite -> Infinite
      | Finite n -> Finite (Z.abs n)

    let print out = function
      | MinusInfinite -> output_string out "-oo"
      | Infinite -> output_string out "+oo"
      | Finite n -> output_string out (Z.to_string n)

  end

  type t =
    | Bottom
    | Interval of (Bounds.t * Bounds.t)
	
  let top = Interval (Bounds.MinusInfinite, Bounds.Infinite)
  let bottom = Bottom

  let const n = Interval (Bounds.Finite n, Bounds.Finite n)
  let rand a b =
    if Z.leq a b
    then Interval (Bounds.Finite a, Bounds.Finite b)
    else Bottom

  let subset a b =
    match (a, b) with
    | (Bottom, _) -> true
    | (Interval _, Bottom) -> false
    | (Interval (la, ha), Interval (lb, hb)) ->
       Bounds.(la >=? lb && ha <=? hb)

  let meet a b =
    match (a, b) with
    | (Bottom, _) | (_, Bottom) -> Bottom
    | (Interval (la, ha), Interval (lb, hb)) ->
       let open Bounds in
       let l = max la lb in
       let h = min ha hb in
       if l <=? h
       then Interval (l, h)
       else Bottom

  let join a b =
    match (a, b) with
    | (Bottom, x) | (x, Bottom) -> x
    | (Interval (la, ha), Interval (lb, hb)) ->
       Interval Bounds.(min la lb, max ha hb)

  module Operators =
  struct
    let cut_neg_pos i =
      match i with
      | Bottom -> (Bottom, Bottom)
      | Interval (a, b) ->
	 let open Bounds in
	 if a >=? Finite Z.zero
	 then (Bottom, Interval (max a (Finite Z.one), b))
	 else if b <=? Finite Z.zero
	 then (Interval (a, min (Finite Z.minus_one) b), Bottom)
	 else (* if a <? (Finite Z.zero) && (Finite Z.zero) <? b *)
	   (Interval (a, Finite Z.minus_one),
	    Interval (Finite Z.one, b))

    let (~-.) v =
      match v with
      | Bottom -> Bottom
      | Interval (a, b) -> Interval Bounds.(~? b, ~? a)

    let (+.) a b =
      match (a, b) with
      | (Bottom, _) | (_, Bottom) -> Bottom
      | (Interval (la, ha), Interval (lb, hb)) ->
	 Interval Bounds.(la +? lb, ha +? hb)

    let (-.) a b = a +. (-. b)

    let ( *. ) a b =
      match (a, b) with
      | (Bottom, _) | (_, Bottom) -> Bottom
      | (Interval (la, ha), Interval (lb, hb)) ->
	 let open List in
	 let products =
	   map (fun x -> map (Bounds.mul x) [lb ; hb]) [la ; ha]
           |> flatten
	 in
	 Interval (fold_left Bounds.min Bounds.Infinite products,
		   fold_left Bounds.max Bounds.MinusInfinite products)

    let ( /. ) a b =
      match (a, b) with
      | (Bottom, _) | (_, Bottom) -> Bottom
      | (Interval (la, ha), Interval (lb, hb)) ->
	 let open Bounds in
	 let (neg, pos) = cut_neg_pos b in
	 let neg_quot =
	   match neg with
	   | Bottom -> Bottom
	   | Interval (ln, hn) ->
	      Interval (min (ha /? ln) (ha /? hn), max (la /? ln) (la /? hn))
	 in
	 let pos_quot =
	   match neg with
	   | Bottom -> Bottom
	   | Interval (lp, hp) ->
	      Interval (min (la /? lp) (la /? hp), max (ha /? lp) (ha /? hp))
	 in	   
	 join neg_quot pos_quot

    let ( %. ) a b =
      match (a, b) with
      | (Bottom, _) | (_, Bottom) -> Bottom
      | (Interval (la, ha), Interval (lb, hb)) ->
	 let open Bounds in
	 if lb = Finite (Z.zero) && hb = Finite (Z.zero)
	 then Bottom
	 else
	   let x = (max (abs lb) (abs hb)) +? (Finite Z.minus_one) in
	   let l = min la (Finite Z.zero) in
	   let h = max ha (Finite Z.zero) in
	   Interval (max l (~? x), min h x)

    let (==.) = meet
    let (!=.) a b =
      match (a, b) with
      | (Bottom, _) | (_, Bottom) -> Bottom
      | (Interval (la, ha), Interval (lb, hb)) ->
	 let open Bounds in
	 if la = ha &&  la = lb && ha = hb
	 then Bottom
	 else Interval (la, ha)

    let (<=.) a b =
      match (a, b) with
      | (Bottom, _) | (_, Bottom) -> Bottom
      | (Interval (la, ha), Interval (lb, hb)) ->
	 let open Bounds in
	 if la >? hb
	 then Bottom
	 else Interval (la, min ha hb)



    let (<.) a b =
      match (a, b) with
      | (Bottom, _) | (_, Bottom) -> Bottom
      | (Interval (la, ha), Interval (lb, hb)) ->
	 let open Bounds in
	 if la >=? hb
	 then Bottom
	 else Interval (la, min ha (pred hb))

    let (>=.) a b =
      match (a, b) with
      | (Bottom, _) | (_, Bottom) -> Bottom
      | (Interval (la, ha), Interval (lb, hb)) ->
	 let open Bounds in
	 if ha <? lb
	 then Bottom
	 else Interval (max la lb, ha)

    let (>.) a b =
      match (a, b) with
      | (Bottom, _) | (_, Bottom) -> Bottom
      | (Interval (la, ha), Interval (lb, hb)) ->
	 let open Bounds in
	 if ha <=? lb
	 then Bottom
	 else Interval (max la (succ lb), ha)


    let bwd_add a b r =
      (meet a (r -. b),
       meet b (r -. a))

    let bwd_sub a b r =
      (meet a (r +. b),
       meet b (a -. r))

    let bwd_mult a b r =
      (meet a (r /. b),
       meet b (r /. a))

    (* Domain [ min i1 ; max i2], where i1 and i2 are domains *)
    let between i1 i2 =
      match (i1, i2) with
      | (Bottom, _) | (_, Bottom) -> Bottom
      | (Interval (l1, _), Interval (_, h2)) ->
	 if Bounds.(l1 <=? h2)
	 then Interval (l1, h2)
	 else Bottom



    (* a/ b = r -> b * r <= a < b * (r+1)
                   b <= a / r && b > a / (r+1) *)
    let bwd_div a b r =
      let bwd_a =
	let (bneg, bpos) = cut_neg_pos b in
	let (rneg, rpos) = cut_neg_pos r in
	[    between (bpos *. rpos) (bpos *. rpos +. bpos -. const Z.one) ;
	     between (bneg *. rneg) (bneg *. rneg -. bneg -. const Z.one) ;
	  -. between (bpos *. (-. rneg)) (bpos *. (-. rneg) +. bpos -. const Z.one) ;
	  -. between ((-. bneg) *. rneg) ((-. bpos) *. rneg -. bpos -. const Z.one) ]
        |> List.map (meet a)
        |> List.fold_left join Bottom
      in
      let bwd_b =
	let one = const Z.one in
	let (aneg, apos) = cut_neg_pos a in
	let (rneg, rpos) = cut_neg_pos r in
	[    between (apos /. (rpos +. one) -. one) (apos /. rpos) ;
	     between (aneg /. (rneg -. one) -. one) (aneg /. rneg) ;
	  -. between (apos /. (-. rneg +. one) -. one) (apos /. (-. rneg)) ;
	  -. between ((-. aneg) /. (rpos +. one) -. one) ((-. aneg) /. rpos) ]
        |> List.map (meet b)
        |> List.fold_left join Bottom
      in
      (bwd_a, bwd_b)

    let bwd_mod a b _ = (a, b)
  end

  let unary v = function
    | AST_UNARY_PLUS -> v
    | AST_UNARY_MINUS -> Operators.(-. v)

  let binary v1 v2 op =
    let cop =
      let open Operators in
      match op with
      | AST_PLUS -> (+.)
      | AST_MINUS -> (-.)
      | AST_MULTIPLY -> ( *. )
      | AST_DIVIDE -> (/.)
      | AST_MODULO -> (%.)
    in cop v1 v2

  let compare v1 v2 op =
    let (cop1, cop2) =
      let open Operators in
      match op with
      | AST_EQUAL -> ((==.), (==.))
      | AST_NOT_EQUAL -> ((!=.), (!=.))
      | AST_LESS -> ((<.), (>.))
      | AST_LESS_EQUAL -> ((<=.), (>=.))
      | AST_GREATER -> ((>.), (<.))
      | AST_GREATER_EQUAL -> ((>=.), (<=.))
    in
    (cop1 v1 v2, cop2 v2 v1)

  let bwd_unary v op r =
    meet v (unary r op)

  let bwd_binary v1 v2 op r =
    let bop =
      let open Operators in
      match op with
      | AST_PLUS -> bwd_add
      | AST_MINUS -> bwd_sub
      | AST_MULTIPLY -> bwd_mult
      | AST_DIVIDE -> bwd_div
      | AST_MODULO -> bwd_mod
    in
    bop v1 v2 r


  let widen a b =
    match (a, b) with
    | (Bottom, x) | (x, Bottom) -> x
    | (Interval (la, ha), Interval (lb, hb)) ->
       let open Bounds in
       let l = if la <=? lb then la else MinusInfinite in
       let h = if ha >=? hb then ha else Infinite in
       Interval (l, h)

  let is_bottom = (=) Bottom

  let print out = function
    | Bottom -> output_string out "Bottom"
    | Interval (a, b) ->
       begin
	 output_string out "[" ;
	 Bounds.print out a ;
	 output_string out "; " ;
	 Bounds.print out b ;
	 output_string out "]"
       end

end

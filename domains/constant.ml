open Value_domain
open Abstract_syntax_tree

module ConstantValueDomain : VALUE_DOMAIN =
struct
  type t =
    | Bottom
    | Value of Z.t
    | Top

  let join x y =
    match (x, y) with
    | (Bottom, _) -> y
    | (_, Bottom) -> x
    | (Value nx, Value ny) when Z.equal nx ny -> Value nx
    | _ -> Top

  let meet x y =
    match (x, y) with
    | (Bottom, _) -> Bottom
    | (_, Bottom) -> Bottom
    | (Value nx, Value ny) ->
       if Z.equal nx ny
       then Value nx
       else Bottom
    | (Top, Value ny) -> Value ny
    | (Value nx, Top) -> Value nx
    | (Top, Top) -> Top


  let on_condition cond x y =
    match (x, y) with
    | (Bottom, _) -> Bottom
    | (_, Bottom) -> Bottom
    | (Value nx, Value ny) ->
       if cond nx ny
       then Value nx
       else Bottom
    | _ -> x



  module Operator =
  struct
    let lift_common op x y =
      match (x, y) with
      | (Bottom, _) -> Bottom
      | (_, Bottom) -> Bottom
      | (Value nx, Value ny) -> op nx ny
      | (Top, _) -> Top
      | (_, Top) -> Top


    let lift op =
      lift_common (fun x y -> Value (op x y))


    let lift_guard op =
      lift_common (fun x y ->
	if Z.equal y Z.zero
	then Bottom
	else Value (op x y)
      )



    let ( +. ) = lift Z.add
    let ( -. ) = lift Z.sub
    let ( *. ) = lift Z.mul
    let ( /. ) = lift_guard Z.div
    let ( %. ) = lift_guard Z.rem

    let ( ==. ) x y = meet x y
    let ( !=. ) = on_condition (fun x y -> not (Z.equal x y))
    let ( <.  ) = on_condition Z.lt
    let ( <=. ) = on_condition Z.leq
    let ( >.  ) = on_condition Z.gt
    let ( >=. ) = on_condition Z.geq
  end




  let top = Top
  let bottom = Bottom

  let const n = Value n
  let rand a b =
    if Z.equal a b
    then Value a
    else Top


  let unary v op =
    match (v, op) with
    | (Bottom, _) -> Bottom
    | (Value n, AST_UNARY_PLUS)  -> Value n
    | (Value n, AST_UNARY_MINUS) -> Value (Z.neg n)
    | (Top, _) -> Top

  let binary v1 v2 op =
    let open Operator in
    let oper = match op with
      | AST_PLUS     -> ( +. )
      | AST_MINUS    -> ( -. )
      | AST_MULTIPLY -> ( *. )
      | AST_DIVIDE   -> ( /. )
      | AST_MODULO   -> ( %. )
    in
    oper v1 v2





  let compare x y op =
    let open Operator in
    let (oper1, oper2) = match op with
      | AST_EQUAL         -> ( (==.), (==.) )
      | AST_NOT_EQUAL     -> ( (!=.), (!=.) )
      | AST_LESS          -> ( (<. ), (>. ) )
      | AST_LESS_EQUAL    -> ( (<=.), (>=.) )
      | AST_GREATER       -> ( (>. ), (<. ) )
      | AST_GREATER_EQUAL -> ( (>=.), (<=.) )
    in (oper1 x y, oper2 y x)

  (* Unary operation are idempotent *)
  let bwd_unary x op r =
    meet x (unary r op)

  (* preimage of x by (fun t -> t * y) *)
  let divide_exact x y =
    match (x, y) with
    | (Bottom, _) -> Bottom
    | (_, Bottom) -> Bottom
    | (Value nx, Value ny) ->
       if nx = Z.zero && ny = Z.zero
       then Top
       else if ny = Z.zero || (Z.rem nx ny <> Z.zero)
       then Bottom
       else Value (Z.div nx ny)
    | (Top, _) -> Top
    | (_, Top) -> Top (* x is non-empty ; thus there is at least 1 and -1 in "x / y"*)


  let bwd_binary x y op r : (t * t) =
    let open Operator in
    match op with
    | AST_PLUS -> (meet x (r -. y),
		   meet y (r -. x))
    (* x - y = r *)
    | AST_MINUS -> (meet x (r +. y),
		    meet y (x -. r))
    (* x * y = r*)
    | AST_MULTIPLY ->
       (meet x (divide_exact r y),
	meet y (divide_exact r x))
    (* x / y = r -> r * y <= x < (r + 1) * y
                    x / (r + 1) < y <= x / r *)
    | AST_DIVIDE ->
       let prex =
	 meet (x >=. r *. y) (x <. (r +. const Z.one) *. y)
       in
       let prey =
	 meet (y >. x /. (r +. const Z.one)) (y <=. x /. r)
       in
       (prex, prey)

    | AST_MODULO ->
       (x, y)
	 
  let widen = join


  let subset x y =
    match (x, y) with
    | (Bottom, _) -> true
    | (Value _, Bottom) -> false
    | (Value nx, Value ny) -> nx = ny
    | (Value _, Top) -> true
    | (Top, _) -> y = Top

  let is_bottom = ((=) Bottom)

  let print out x =
    match x with
    | Top -> output_string out "Top"
    | Bottom -> output_string out "Bottom"
    | Value x -> output_string out ("(Value " ^ Z.to_string x ^ ")")
end

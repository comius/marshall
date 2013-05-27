module Make = functor (D : Dyadic.DYADIC) ->
struct
  module S = Syntax.Make(D)
  module I = Interval.Make(D)  
  
  type expr =
    | Real of arithmetic
    | Sigma of sigma
    | Tuple of expr list (* [(e1, ..., en)] *)
    | Unconverted of S.expr

  and arithmetic =
    | Var of S.name
    | RealVar of S.name * I.t (* real variable with a given range, see [Eval.refine] *)
    | Dyadic of D.t (* dyadic constant, syntax as in MPFR (subsumes floating-point) *)
    | Interval of I.t (* interval constant, no concrete syntax *)
    | Cut of S.name * I.t * sigma * sigma
	(* [Cut (x, [a, b], l, u)] is the real number in interval
	   $[a,b]$ whose lower cut is $\lambda x, l$ and upper cut is
	   $\lambda x, u$. There are three kinds of concrete syntax:
	   \begin{itemize}
	   \item [cut x left l right u]
	   \item [cut x : real left l right u]
	   \item [cut x : [a,b] left l right u]
	   \end{itemize} *)
    | Binary of S.binary * arithmetic * arithmetic
    | Unary of S.unary * arithmetic
    | Power of arithmetic * int (* Power by a natural constant *)

  and sigma =
    | True
    | False
    | Less of arithmetic * arithmetic
	(* Apart from [a < b], concrete syntax also has sugars [a > b]
	   and $a ={e}= b$, which means $-e < a - b < e$. *)
    | And of sigma list (* [p1 /\ p2 /\ ... /\ pn] *)
    | Or of sigma list (* [p1 \/ p2 \/ ... \/ pn] *)
    | Exists of S.name * I.t * sigma (* [exists x : [a,b], p] *)
    | Forall of S.name * I.t * sigma (* [forall x : [a,b], p] *)

  and arrow = 
     S.name * S.ty * expr (* Concrete syntax is [fun x : ty => e] *)

  and tuple =
     expr list (* [(e1, ..., en)] *)

  let error = Message.runtime_error

   let proj e k =
    match e with
      | Tuple lst ->
         (try
            List.nth lst k
          with Failure _ -> error "Tuple too short")
      | _ -> error "Tuple expected"
	
  let rec convert env e = match e with    
    | S.Proj (e, k) -> 
	    (match convert env e with
	       | Tuple _ as e' -> proj e' k
	       | _ -> Unconverted e)
    | S.Lambda _ -> Unconverted e
    | S.Let (x, e1, e2) -> 
	    let e1' = convert env e1 in
	      convert ((x,e1')::env) e2
    | S.App (e1, e2)  ->
	    let e2' = convert env e2 in
	      (match convert env e1 with
		| (Unconverted (S.Lambda (x, ty, e))) -> convert ((x,e2')::env) e
		| e1' -> Unconverted (S.App (e1, e2)))
    | S.Tuple lst -> Tuple (List.map (convert env) lst)

    | S.True _ | S.False _ | S.Less _ | S.And _ | S.Or _ | S.Exists _ | S.Forall _ as e -> Sigma(convert_sigma env e)
    | S.Dyadic _ | S.Cut _ | S.Binary _ | S.Unary _ | S.Power _ as e -> Real(convert_real env e)	
    | S.Var x -> (try
	       List.assoc x env
	     with Not_found ->
	       error ("Unknown variable " ^ S.string_of_name x))
  and
    convert_real env e = match e with
	| S.Dyadic d -> Dyadic d	
	| S.Cut (x, i, p1, p2) ->	    
	      Cut (x, i, convert_sigma ((x,Real (Var x))::env) p1, convert_sigma ((x,Real (Var x))::env) p2)
	| S.Binary (op, e1, e2) -> Binary (op, convert_real env e1, convert_real env e2)
	| S.Unary (op, e) -> Unary (op, convert_real env e)
	| S.Power (e, k) -> Power (convert_real env e, k)
	| _ -> (match convert env e with
	    | Real e -> e
	    | _ -> error ("typecheck" ^ S.string_of_expr e))
  and
    convert_sigma env e = match e with
	| S.True -> True
	| S.False -> False
	| S.Less (e1, e2) -> Less (convert_real env e1, convert_real env e2)
	| S.And lst -> And (List.map (convert_sigma env) lst)
	| S.Or lst -> Or (List.map (convert_sigma env) lst)
	| S.Exists (x, i, e) -> Exists (x, i, convert_sigma ((x,Real (Var x))::env) e)
	| S.Forall (x, i, e) -> Forall (x, i, convert_sigma ((x,Real (Var x))::env) e)	  
	| _ -> (match convert env e with
	    | Sigma s -> s
	    | _ -> error ("typecheck" ^ S.string_of_expr e))           

 (** Convert a string to expression *)
  let rec string_of_expr e =
    let rec to_str n e =
      let (m, str) =
	match e with
	  | Real e' -> (match e' with
	    | Var x   ->           (100, S.string_of_name x)
	    | RealVar (x, i) ->    (100, "(" ^ S.string_of_name x ^ ":" ^ I.to_string i ^ ")")
	    | Dyadic q ->          (100, D.to_string q)
	    | Interval i ->        (100, I.to_string_number i)
	    | Power (e'', k) ->      (83, to_str 82 (Real e'') ^ " ^ " ^ string_of_int k)
	    | Unary (op, e'') ->     (80, S.string_of_unary op ^ " " ^ to_str 80 (Real e''))
	    | Binary (op, e1, e2) ->
	      let p, p1, p2 = S.precs_of_binary op in
		(p, to_str p1 (Real e1) ^ " " ^ S.string_of_binary op ^ " " ^ to_str p2 (Real e2))
	    | Cut (x, i, p1, p2) -> (5, "cut " ^ S.string_of_name x ^ " : " ^
				     I.to_string i ^
				     " left " ^ to_str 5 (Sigma p1) ^ " right " ^ to_str 5 (Sigma p2))
	  )
	  | Sigma e' -> (match e' with 
	    | True | And [] ->     (100, "True")
	    | False | Or [] ->     (100, "False")
	    | Less (e1, e2) ->     (30, to_str 30 (Real e1) ^ " < " ^ to_str 30 (Real e2))
	    | And lst ->           (20, String.concat " /\\ " (List.map (fun x -> to_str 19 (Sigma x)) lst))
	    | Or lst ->            (15, String.concat " \\/ " (List.map (fun x -> to_str 14 (Sigma x)) lst))
	    | Exists (x, t, p) ->  (10, "exists " ^ S.string_of_name x ^ " : " ^
				      I.to_string t ^ " , " ^ to_str 9 (Sigma p))
	    | Forall (x, t, p) ->  (10, "forall " ^ S.string_of_name x ^ " : " ^
				      I.to_string t ^ " , " ^ to_str 9 (Sigma p))	  
	  )
	  | Tuple lst ->         (100, "(" ^ (String.concat ", " (List.map (to_str 10) lst)) ^ ")")
	  | Unconverted e -> (10, "["^(S.string_of_expr e)^"]")
      in
	if m > n then str else "(" ^ str ^ ")"
    in
      to_str (-1) e

end;;
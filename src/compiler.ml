module Make = functor (D : Dyadic.DYADIC) ->
struct
  module S = Syntax.Make(D)
  module I = Interval.Make(D)  
  
  type expr =    
    | Real of realexpr * basesets (* another realexpr for Lifschitz *)
    | Sigma of sigmaexpr * basesets
    | Tuple of expr list (* [(e1, ..., en)] *)
    | Uncompiled of S.expr  
  and realexpr = 
    | EnvRVar of S.name 
    | BsRVar of S.name
    | Binary of binaryop * realexpr * realexpr 
    | Unary of unaryop * realexpr     
    | ConstReal of D.t
  and sigmaexpr = 
    | BsBVar of S.name 
    | And of sigmaexpr list
    | Or of sigmaexpr list
    | Less of realexpr * realexpr
    | ConstSigma of bool
  and basesets = (S.name * bs) list
  and bs = 
    | Exists of S.name * (I.t * basesets) list (*ref*) * sigmaexpr
    | Forall of S.name * (I.t * basesets) list (*ref*) * sigmaexpr
    | Cut of S.name * I.t (*ref*) * basesets * basesets * sigmaexpr * sigmaexpr  
  and binaryop = prec:int -> round:D.rounding_mode -> I.t -> I.t -> I.t
  and unaryop = prec:int -> round:D.rounding_mode -> I.t -> I.t

  let error = Message.runtime_error

  let proj e k =
    match e with
      | Tuple lst ->
         (try
            List.nth lst k
          with Failure _ -> error "Tuple too short")
      | _ -> error "Tuple expected"

  let make_prec prec i =
    let w = I.width ~prec:2 ~round:D.up i in
    let e1 = D.get_exp w in
    let e2 = max (D.get_exp (I.lower i)) (D.get_exp (I.upper i)) in
      max 2 (max prec (- 5 * (e1 - e2) / 4))

	
  let rec compile env e = match e with    
    | S.Proj (e, k) -> 
	    (match compile env e with
	       | Tuple _ as e' -> proj e' k
	       | _ -> Uncompiled e)
    | S.Lambda _ -> Uncompiled e
    | S.Let (x, e1, e2) -> 
	    let e1' = compile env e1 in
	      compile ((x,e1')::env) e2
    | S.App (e1, e2)  ->
	    let e2' = compile env e2 in
	      (match compile env e1 with
		| (Uncompiled (S.Lambda (x, ty, e))) -> compile ((x,e2')::env) e
		| e1' -> Uncompiled (S.App (e1, e2)))
    | S.Tuple lst -> Tuple (List.map (compile env) lst)
    
    | S.Dyadic _ | S.Cut _ | S.Binary _ | S.Unary _ | S.Power _ as e -> 
	let r,bs = compile_real env e in  Real (r,bs)
    | S.True _ | S.False _ | S.Less _ | S.And _ | S.Or _ | S.Exists _ | S.Forall _ as e -> 
	let s,bs = compile_sigma env e in Sigma (s,bs)
    | S.Var x -> (try
	       List.assoc x env
	     with Not_found ->
	       error ("Unknown variable " ^ S.string_of_name x))
  and 
    getx x env = List.assoc x env
  and
    compile_real env e = match e with
	| S.Dyadic d -> 
	      ConstReal d, []
	| S.Cut (x, i, p1, p2) ->	    	    	    
	    let s1,bs1 = compile_sigma ((x,realvar x)::env) p1 in
	    let s2,bs2 = compile_sigma ((x,realvar x)::env) p2 in
	    let y = S.fresh_name "c" in
	      BsRVar y, [(y,Cut (x,i,bs1,bs2,s1,s2))]
	| S.Binary (op, e1, e2) -> 
	    let r1,bs1 = compile_real env e1 in
	    let r2,bs2 = compile_real env e2 in	    
	    let opf = (match op with
	      | S.Plus -> I.add 
	      | S.Minus -> I.sub
	      | S.Times -> I.mul
	      | S.Quotient -> I.div) in
	    Binary (opf, r1, r2), bs1@bs2	    
	| S.Unary (op, e) ->	    
	    let r1,bs1 = compile_real env e in	    
	    let opf = (match op with
	      | S.Opposite -> I.neg 
	      | S.Inverse -> I.inv) in
	      Unary (opf, r1), bs1
	| S.Power (e, k) ->	    
	    let r1,bs1 = compile_real env e in	    
	      Unary ((fun ~prec ~round i -> I.pow ~prec ~round i k),r1), bs1	      
	| _ -> (match compile env e with
	    | Real (r,bs) -> r,bs
	    | _ -> error ("typecheck" ^ S.string_of_expr e))
  and
    realvar x = Real (EnvRVar x, [])  
  and
    compile_sigma env e = match e with
	| S.True -> ConstSigma true, []
	| S.False -> ConstSigma false, []
	| S.Less (e1, e2) -> 	    
	    let r1,bs1 = compile_real env e1 in
	    let r2,bs2 = compile_real env e2 in
	    Less (r1,r2), bs1@bs2
	| S.And lst -> 
	    let r,bs = List.split (List.map (compile_sigma env) lst) in
	    And r, List.flatten bs
	| S.Or lst -> 
	    let r,bs = List.split (List.map (compile_sigma env) lst) in
	    Or r, List.flatten bs
	| S.Exists (x, i, e) -> 	    
	    let s,bs = compile_sigma ((x,realvar x)::env) e in
	    let y = S.fresh_name "e" in
	    BsBVar y, [(y,Exists (x,[i,bs],s))]
	| S.Forall (x, i, e) -> 
	    let s,bs = compile_sigma ((x,realvar x)::env) e in
	    let y = S.fresh_name "a" in
	    BsBVar y, [(y,Forall (x,[i,bs],s))]
	| _ -> (match compile env e with
	    | Sigma (s,bs) -> s,bs
	    | _ -> error ("typecheck" ^ S.string_of_expr e))           

 (** Convert a string to expression *)
  let rec string_of_expr e =
    match e with
	  | Real (r,bs) -> "real " ^ str_of_bs bs ^ " in " ^ str_of_real r 
	  | Sigma (s,bs) -> "sigma " ^ str_of_bs bs ^ " in " ^ str_of_sigma s 
	  | Tuple lst -> "(" ^ (String.concat ", " (List.map string_of_expr lst)) ^ ")"
	  | Uncompiled e -> "["^(S.string_of_expr e)^"]"
   and str_of_bs bs = "(" ^ String.concat ", " (List.map str_of_env bs) ^ ")"
   and str_of_ibs ibslst = "(" ^ String.concat ", " (List.map (fun (i,bs) -> I.to_string i ^ str_of_bs bs) ibslst) ^ ")"
   and str_of_env env = match env with
      | y,Forall (x, ibs, s) -> (S.string_of_name y) ^ " = forall " ^ (S.string_of_name x) ^ ":" ^ str_of_ibs ibs ^ " in " ^ str_of_sigma s
      | y,Exists (x, ibs, s) -> (S.string_of_name y) ^ " = exists " ^ (S.string_of_name x) ^ ":" ^ str_of_ibs ibs ^ " in " ^ str_of_sigma s
      | y,Cut (x, i, bs1, bs2,s1,s2) -> (S.string_of_name y) ^ " = cut " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ 
	    " left " ^ str_of_bs bs1 ^ " in " ^ str_of_sigma s1 ^ 
	    " right " ^ str_of_bs bs2 ^ " in " ^ str_of_sigma s2
  and str_of_real r = match r with
    | EnvRVar x -> S.string_of_name x 
    | BsRVar x -> S.string_of_name x 
    | Binary (_,r1,r2) -> (str_of_real r1) ^ "°" ^ (str_of_real r2)
    | Unary (_,r1) -> str_of_real r1    
    | ConstReal c -> D.to_string c
  and str_of_sigma s = match s with
    | BsBVar x -> S.string_of_name x 
    | And lst -> String.concat "/\\" (List.map str_of_sigma lst)
    | Or lst -> String.concat "\\/" (List.map str_of_sigma lst)
    | Less (r1,r2) -> (str_of_real r1) ^ "<" ^ (str_of_real r2)
    | ConstSigma c -> string_of_bool c

end;;
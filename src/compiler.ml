module Make = functor (D : Dyadic.DYADIC) ->
struct
  module S = Syntax.Make(D)
  module I = Interval.Make(D)  
  
  type expr =    
    | Real of eval_real * refine * basesets
    | Sigma of approx * approx * refine * basesets
    | Tuple of expr list (* [(e1, ..., en)] *)
    | Uncompiled of S.expr  
  and eval_real = prec:int -> round:D.rounding_mode -> basesets -> I.t
  and approx = basesets -> bool
  and refine = basesets -> basesets
  and basesets = env list
  and env = Quant of S.name * I.t * basesets | Cut of S.name * I.t * basesets * basesets   

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
	let est,r,bs = compile_real env e in  Real (est,r,bs)
    | S.True _ | S.False _ | S.Less _ | S.And _ | S.Or _ | S.Exists _ | S.Forall _ as e -> 
	let u,l,r,bs = compile_sigma env e in Sigma (u,l,r,bs)
    | S.Var x -> (try
	       List.assoc x env
	     with Not_found ->
	       error ("Unknown variable " ^ S.string_of_name x))
  and
    idref = fun bs -> bs  
  and 
    getx x bs = match bs with | (Quant (x,i,_))::tail -> i  | (Cut (x,i,_,_))::tail -> i | _::tail -> getx x tail | [] -> error ("getx")
  and
    compile_real env e = match e with
	| S.Dyadic d -> let i = I.of_dyadic d in 
	      (fun ~prec ~round bs -> i), idref, []
	| S.Cut (x, i, p1, p2) ->	    	    	    
	    let _,_,_,bs1 = compile_sigma ((x,realvar x)::env) p1 in
	    let _,_,_,bs2 = compile_sigma ((x,realvar x)::env) p2 in
	      (fun ~prec ~round bs -> getx x bs), idref, [Cut (x,i,bs1,bs2)]
	| S.Binary (op, e1, e2) -> 
	    let est1,r1,bs1 = compile_real env e1 in
	    let est2,r2,bs2 = compile_real env e2 in	    
	    let opf = (match op with
	      | S.Plus -> I.add 
	      | S.Minus -> I.sub
	      | S.Times -> I.mul
	      | S.Quotient -> I.div) in
	      (fun ~prec ~round bs -> opf ~prec ~round (est1 ~prec ~round bs) (est2 ~prec ~round bs)),
		  idref,
		  bs1@bs2
	| S.Unary (op, e) ->	    
	    let est1,r1,bs1 = compile_real env e in	    
	    let opf = (match op with
	      | S.Opposite -> I.neg 
	      | S.Inverse -> I.inv) in
	      (fun ~prec ~round bs -> opf ~prec ~round (est1 ~prec ~round bs)),
		idref,
		bs1
	| S.Power (e, k) ->	    
	    let est1,r1,bs1 = compile_real env e in	    
	      (fun ~prec ~round bs -> I.pow ~prec ~round (est1 ~prec ~round bs) k), idref, bs1
	| _ -> (match compile env e with
	    | Real (est,r,bs) -> est,r,bs
	    | _ -> error ("typecheck" ^ S.string_of_expr e))
  and
    realvar x = Real ((fun ~prec ~round bs -> getx x bs), idref, [])
  and
    compile_sigma env e = match e with
	| S.True -> ((fun bs -> true), (fun bs -> true), idref, [])
	| S.False -> ((fun bs -> false), (fun bs -> false), idref, [])
	| S.Less (e1, e2) -> 	    
	    let est1,r1,bs1 = compile_real env e1 in
	    let est2,r2,bs2 = compile_real env e1 in	
	    ((fun bs -> 
	      let i1 = est1 ~prec:1 ~round:D.down bs in
	      let i2 = est2 ~prec:1 ~round:D.down bs in D.lt (I.upper i1) (I.lower i2)),
		    (fun bs -> 
	      let i1 = est1 ~prec:1 ~round:D.up bs in
	      let i2 = est2 ~prec:1 ~round:D.up bs in D.lt (I.upper i1) (I.lower i2)),
	      idref, bs1@bs2)
	| S.And lst -> let lst = (List.map (compile_sigma env) lst) in
	  let lower = List.fold_left (fun h x -> let l,u,r,bs = x in fun bs -> h bs && l bs) (fun env -> true) lst in
	  let upper = List.fold_left (fun h x -> let l,u,r,bs = x in fun bs -> h bs && u bs) (fun env -> true) lst in
	  let bs = List.fold_left (fun h x -> let l,u,r,bs = x in h@bs) [] lst in
	    (lower, upper, idref, bs)	    
	| S.Or lst -> let lst = (List.map (compile_sigma env) lst) in
	  let lower = List.fold_left (fun h x -> let l,u,r,bs = x in fun bs -> h bs || l bs) (fun env -> false) lst in
	  let upper = List.fold_left (fun h x -> let l,u,r,bs = x in fun bs -> h bs || u bs) (fun env -> false) lst in
	  let bs = List.fold_left (fun h x -> let l,u,r,bs = x in h@bs) [] lst in
	    (lower, upper, idref, bs)	    	    
	| S.Exists (x, i, e) -> 	    
	    let l,u,r,bs = compile_sigma ((x,realvar x)::env) e in
	    ((fun bs -> true), (fun bs-> false), idref, [Quant (x,i,bs)])
	    (*let est1,r1,bs1 = commonreal real1 in
	    let s,l,u = compile_sigma ((x,realvar x)::env) e in
	      ([Quant (x,[(i,s)])], (fun env -> let m = I.of_dyadic (I.midpoint ~prec:1 1 (List.assoc x env)) in l ((x,m)::env)),
			fun env -> let j = I.flip (List.assoc x env) in u ((x,j)::env))*)
	| S.Forall (x, i, e) -> (*Forall (x, i, compile_sigma ((x,realvar x)::env) e)	  *)	    
	    let l,u,r,bs = compile_sigma ((x,realvar x)::env) e in
	    ((fun bs -> true), (fun bs-> false), idref, [Quant (x,i,bs)])

(*	    let s,l,u = compile_sigma ((x,realvar x)::env) e in
	      ([Quant (x,[(i,s)])], (fun env -> let m = I.of_dyadic (I.midpoint ~prec:1 1 (List.assoc x env)) in l ((x,m)::env)),
			fun env -> let j = I.flip (List.assoc x env) in u ((x,j)::env))*)
	| _ -> (match compile env e with
	    | Sigma (u,l,e,bs) -> u,l,e,bs
	    | _ -> error ("typecheck" ^ S.string_of_expr e))           

 (** Convert a string to expression *)
  let rec string_of_expr e =
    match e with
	  | Real (_,_,bs) -> "real: " ^ str_of_bs bs 
	  | Sigma (_,_,_,bs) -> "sigma: " ^ str_of_bs bs
	  | Tuple lst -> "(" ^ (String.concat ", " (List.map string_of_expr lst)) ^ ")"
	  | Uncompiled e -> "["^(S.string_of_expr e)^"]"
   and str_of_bs bs = "(" ^ String.concat ", " (List.map str_of_env bs) ^ ")"
   and str_of_env env = match env with
      | Quant (x, i, bs) -> "q " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ str_of_bs bs
      | Cut (x, i, bs1, bs2) -> "cut " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ " left " ^ str_of_bs bs1 ^ " right " ^ str_of_bs bs2
  
end;;
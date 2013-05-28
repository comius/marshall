module Make = functor (D : Dyadic.DYADIC) ->
struct
  module S = Syntax.Make(D)
  module I = Interval.Make(D)  
  
  type expr =    
    | Real of eval_real * refine * basesets
    | Sigma of approx * approx * refine * basesets
    | Tuple of expr list (* [(e1, ..., en)] *)
    | Uncompiled of S.expr  
  and eval_real = prec:int -> round:D.rounding_mode -> env -> basesets -> I.t
  and approx = prec:int -> env -> basesets -> bool
  and refine = k:int -> prec:int -> env -> basesets -> basesets
  and basesets = bs list
  and bs = Quant of S.name * (I.t * basesets) list | Cut of S.name * I.t * basesets * basesets   
  and env = (S.name * I.t) list
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
	let est,r,bs = compile_real env e in  Real (est,r,bs)
    | S.True _ | S.False _ | S.Less _ | S.And _ | S.Or _ | S.Exists _ | S.Forall _ as e -> 
	let u,l,r,bs = compile_sigma env e in Sigma (u,l,r,bs)
    | S.Var x -> (try
	       List.assoc x env
	     with Not_found ->
	       error ("Unknown variable " ^ S.string_of_name x))
  and
    idref = fun ~k ~prec env bs -> bs  
  and
    cutref l1 r1 l2 r2 = fun ~k ~prec env bs -> 
	    match bs with
	    | [Cut (x,i,bs1,bs2)] ->
	      let prec = make_prec prec i in
		(* To refine a cut [Cut(x,i,p1,p2)] we try to make the
		   interval [i] smaller and refine [p1] and [p2]. *)
	      let a = I.lower i in
	      let b = I.upper i in
		(* Bisection *)
	      let m1, m2 = I.thirds prec k i in
	      let a' = (if l1 ~prec ((x,I.of_dyadic m1)::env) bs1 then m1 else a) in
	      let b' = (if l2 ~prec ((x,I.of_dyadic m2)::env) bs2 then m2 else b) in
	      let j = I.make a' b' in 	    
	      let env' = (x,j)::env in
	      let q1 = r1 ~k ~prec env' bs1 in
	      let q2 = r2 ~k ~prec env' bs2 in
	      [Cut (x,j,q1,q2)] 
	  | _ -> error "cutref"
  and 
    partitionlist len lst = 
      if len == 0 then [],lst
      else
	match lst with 
	  | h::tl -> let a,b = partitionlist (len-1) tl in (h::a),b
	  | _ -> error "partitionlist"
  and
    binref l1 r1 r2 = fun ~k ~prec env bs -> let bs1,bs2 = partitionlist l1 bs in (r1 ~k ~prec env bs1) @ (r2 ~k ~prec env bs2)
  and 
    getx x env = List.assoc x env
  and
    compile_real env e = match e with
	| S.Dyadic d -> let i = I.of_dyadic d in 
	      (fun ~prec ~round env bs -> i), idref, []
	| S.Cut (x, i, p1, p2) ->	    	    	    
	    let l1,_,r1,bs1 = compile_sigma ((x,realvar x)::env) p1 in
	    let l2,_,r2,bs2 = compile_sigma ((x,realvar x)::env) p2 in
	      (fun ~prec ~round env bs -> match bs with | (Cut (_,i,_,_))::_ -> i | _ -> error ""), 
	      (cutref l1 r1 l2 r2), 
	      [Cut (x,i,bs1,bs2)]
	| S.Binary (op, e1, e2) -> 
	    let est1,r1,bs1 = compile_real env e1 in
	    let est2,r2,bs2 = compile_real env e2 in	    
	    let opf = (match op with
	      | S.Plus -> I.add 
	      | S.Minus -> I.sub
	      | S.Times -> I.mul
	      | S.Quotient -> I.div) in
	    let l1 = List.length bs1 in
	      (fun ~prec ~round env bs -> let bs1,bs2 = partitionlist l1 bs in opf ~prec ~round (est1 ~prec ~round env bs1) (est2 ~prec ~round env bs2)),
		  binref l1 r1 r2,
		  bs1@bs2
	| S.Unary (op, e) ->	    
	    let est1,r1,bs1 = compile_real env e in	    
	    let opf = (match op with
	      | S.Opposite -> I.neg 
	      | S.Inverse -> I.inv) in
	      (fun ~prec ~round env bs -> opf ~prec ~round (est1 ~prec ~round env bs)),
		r1,
		bs1
	| S.Power (e, k) ->	    
	    let est1,r1,bs1 = compile_real env e in	    
	      (fun ~prec ~round env bs -> I.pow ~prec ~round (est1 ~prec ~round env bs) k),
	      r1, bs1
	| _ -> (match compile env e with
	    | Real (est,r,bs) -> est,r,bs
	    | _ -> error ("typecheck" ^ S.string_of_expr e))
  and
    realvar x = Real ((fun ~prec ~round env bs -> getx x env), idref, [])
  and
    foldop op sop env lst = match lst with
      | h::tl -> let l1,u1,r1,bs1 = compile_sigma env h in
		let l2,u2,r2,bs2 = foldop op sop env tl in
		let len1= List.length bs1 in
		(fun  ~prec env bs -> let bs1,bs2 = partitionlist len1 bs in op (l1  ~prec env bs1) (l2  ~prec env bs2)),
		(fun  ~prec env bs -> let bs1,bs2 = partitionlist len1 bs in op (l1  ~prec env bs1) (l2  ~prec env bs2)),
		binref len1 r1 r2,
		bs1@bs2
      | [] -> (fun  ~prec env bs -> sop), (fun  ~prec env bs -> sop), idref, []
  and
    compile_sigma env e = match e with
	| S.True -> ((fun ~prec env bs -> true), (fun  ~prec env bs -> true), idref, [])
	| S.False -> ((fun  ~prec env bs -> false), (fun  ~prec env bs -> false), idref, [])
	| S.Less (e1, e2) -> 	    
	    let est1,r1,bs1 = compile_real env e1 in
	    let est2,r2,bs2 = compile_real env e2 in
	    let l1 = List.length bs1 in
	    ((fun ~prec env bs -> 
	      let bs1,bs2 = partitionlist l1 bs in
	      let i1 = est1 ~prec ~round:D.down env bs1 in
	      let i2 = est2 ~prec ~round:D.down env bs2 in 
		  D.lt (I.upper i1) (I.lower i2)) , 
		    (fun ~prec env bs -> 
	      let bs1,bs2 = partitionlist l1 bs in
	      let i1 = est1 ~prec ~round:D.up env bs1 in
	      let i2 = est2 ~prec ~round:D.up env bs2 in D.lt (I.upper i1) (I.lower i2)),
	      binref l1 r1 r2, bs1@bs2)
	| S.And lst -> 
	    foldop (&&) true env lst
	| S.Or lst -> 
	    foldop (||) false env lst
	| S.Exists (x, i, e) -> 	    
	    let l,u,r,bs = compile_sigma ((x,realvar x)::env) e in
	    ((fun  ~prec env bs -> true), (fun  ~prec env bs-> false), idref, [Quant (x,[i,bs])])
	    (*let est1,r1,bs1 = commonreal real1 in
	    let s,l,u = compile_sigma ((x,realvar x)::env) e in
	      ([Quant (x,[(i,s)])], (fun env -> let m = I.of_dyadic (I.midpoint ~prec:1 1 (List.assoc x env)) in l ((x,m)::env)),
			fun env -> let j = I.flip (List.assoc x env) in u ((x,j)::env))*)
	| S.Forall (x, i, e) -> (*Forall (x, i, compile_sigma ((x,realvar x)::env) e)	  *)	    
	    let l,u,r,bs = compile_sigma ((x,realvar x)::env) e in
	    ((fun  ~prec env bs -> true), (fun  ~prec env bs-> false), idref, [Quant (x,[i,bs])])

(*	    let s,l,u = compile_sigma ((x,realvar x)::env) e in
	      ([Quant (x,[(i,s)])], (fun env -> let m = I.of_dyadic (I.midpoint ~prec:1 1 (List.assoc x env)) in l ((x,m)::env)),
			fun env -> let j = I.flip (List.assoc x env) in u ((x,j)::env))*)
	| _ -> (match compile env e with
	    | Sigma (u,l,e,bs) -> u,l,e,bs
	    | _ -> error ("typecheck" ^ S.string_of_expr e))           

 (** Convert a string to expression *)
  let rec string_of_expr e =
    match e with
	  | Real (e,_,bs) -> let i = e ~prec:32 ~round:D.down [] bs in	"real " ^ I.to_string_number i ^ ":" ^ str_of_bs bs 
	  | Sigma (_,_,_,bs) -> "sigma: " ^ str_of_bs bs
	  | Tuple lst -> "(" ^ (String.concat ", " (List.map string_of_expr lst)) ^ ")"
	  | Uncompiled e -> "["^(S.string_of_expr e)^"]"
   and str_of_bs bs = "(" ^ String.concat ", " (List.map str_of_env bs) ^ ")"
   and str_of_quant ibslst = "(" ^ String.concat ", " (List.map (fun (i,bs) -> I.to_string i ^ str_of_bs bs) ibslst) ^ ")"
   and str_of_env env = match env with
      | Quant (x, ibs) -> "q " ^ (S.string_of_name x) ^ ":" ^ str_of_quant ibs
      | Cut (x, i, bs1, bs2) -> "cut " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ " left " ^ str_of_bs bs1 ^ " right " ^ str_of_bs bs2

  let target_precision = ref (D.make_int ~prec:10 ~round:D.up 1 (-52))

  let exec trace e =  
    let rec loop k p e' =
      if trace then
	begin
	  print_endline ("--------------------------------------------------\n" ^
			   "Iteration: " ^ string_of_int k ^ "\n" ^
			   string_of_expr e' ^ "\n" ^
			   "Press Enter to continue " 
			) ;
	  ignore (read_line ())	  
	end ;
      match e' with
	| Real (e,r,bs) ->
	    let i = e ~prec:p ~round:D.down [] bs in	       
	    let w = (I.width 10 D.up i) in	    
	      if D.lt w !target_precision then
		(e', Real (e,r,bs))
	      else
		loop (k+1) (make_prec (p+3) (I.make D.zero !target_precision)) (Real (e,r,r ~k ~prec:p [] bs))		
	|  _ -> (e', e')
    in            
      loop 1 32 e

  
end;;
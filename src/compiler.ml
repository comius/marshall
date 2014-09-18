module Make = functor (D : Dyadic.DYADIC) ->
struct
  module S = Syntax.Make(D)
  module I = Interval.Make(D)  
  
  type expr =    
    | Real of realexpr * realexpr * basesets (* another realexpr for Lipschitz *)
    | Sigma of sigmaexpr * basesets
    | Tuple of expr list (* [(e1, ..., en)] *)
    | Uncompiled of S.expr  
  and realexpr = 
    | EnvRVar of int
    | EnvDRVar of int
    | BsRVar of int
    | Binary of binaryop * realexpr * realexpr 
    | Unary of unaryop * realexpr     
    | ConstReal of I.t
  and sigmaexpr = 
    | BsBVar of int
    | And of sigmaexpr list
    | Or of sigmaexpr list
    | GtZero of realexpr * realexpr
    | ConstSigma of bool
  and basesets = bs list
  and bs = 
    | Exists of (I.t * int * basesets) list (*ref*) * sigmaexpr
    | Forall of (I.t * int * basesets) list (*ref*) * sigmaexpr
    | Cut of I.t (*ref*) * basesets * basesets * sigmaexpr * sigmaexpr  
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

(* newenv adds a new real variable to the environment with de Bruijin index 0 and increases all other variables *)
  let rec 
    newenv env x = (x,Real (EnvRVar 0, EnvDRVar 0, []))::List.map (fun (x,e) -> (x, incre e)) env	
  and
    incre e = match e with
      | Real (x,y,bs) -> Real (incr x, incr y, bs)
      | Sigma (x,bs) -> Sigma (incs x,bs)
      | Tuple lst -> Tuple (List.map incre lst)
      | e -> e
  and 
    incr e = match e with
      | EnvRVar i -> EnvRVar (i+1)
      | EnvDRVar i -> EnvDRVar (i+1)      
      | Binary(op,x,y) -> Binary (op,incr x, incr y)
      | Unary (op,x) -> Unary (op, x)
      | e -> e
  and
    incs e = match e with
      | And lst -> And (List.map incs lst)
      | Or lst -> Or (List.map incs lst)    
      | GtZero (x,y) -> GtZero(incr x, incr y)
      | e -> e      


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
	let r,l,bs = compile_real env e 0 in  Real (r,l,bs)
    | S.True _ | S.False _ | S.Less _ | S.And _ | S.Or _ | S.Exists _ | S.Forall _ as e -> 
	let s,bs = compile_sigma env e 0 in Sigma (s,bs)
    | S.Var x -> (try
	       List.assoc x env
	     with Not_found ->
	       error ("Unknown variable " ^ S.string_of_name x))  
  and
    powk k = fun ~prec ~round i -> I.pow ~prec ~round i k
  and
    compile_real env e bs0 = match e with
	| S.Dyadic d -> 
	      ConstReal (I.of_dyadic d), ConstReal (I.of_dyadic D.zero), []
	| S.Cut (x, i, p1, p2) ->	    	    	    
	    let s1,bs1 = compile_sigma (newenv env x) p1 0 in	    
	    let s2,bs2 = compile_sigma (newenv env x) p2 0 in	    
	      BsRVar 0, ConstReal I.bottom, [Cut (i,bs1,bs2,s1,s2)]
	| S.Binary (op, e1, e2) -> 
	    let r1,l1,bs1 = compile_real env e1 bs0 in
	    let bs0 = bs0 + List.length bs1 in
	    let r2,l2,bs2 = compile_real env e2 bs0 in	    
	    let opf,l = (match op with
	      | S.Plus -> I.add, Binary (I.add,l1,l2)
	      | S.Minus -> I.sub, Binary (I.sub,l1,l2)
	      | S.Times -> I.mul, Binary (I.add, Binary (I.mul,l1,r2), Binary (I.mul,r1,l2))
	      | S.Quotient -> I.div, Binary (I.div, 
		Binary (I.sub,Binary (I.mul,l1,r2),Binary(I.mul,l2,r1)),
		Unary(powk 2, r1))) in
	    Binary (opf, r1, r2),l, bs1@bs2	    
	| S.Unary (op, e) ->	    
	    let r1,l1,bs1 = compile_real env e bs0 in	    
	    let opf,l = (match op with
	      | S.Opposite -> I.neg, Unary (I.neg, l1)
	      | S.Inverse -> I.inv, Unary (I.neg, Binary (I.div, l1, Unary (powk 2,r1)))) in
	      Unary (opf, r1), l, bs1
	| S.Power (e, k) ->	    
	    let r1,l1,bs1 = compile_real env e bs0 in Unary (powk k,r1), 
		Binary (I.mul, ConstReal (I.of_dyadic (D.of_int ~round:D.down k)), 
				Binary (I.mul, Unary (powk (k-1), r1), l1)),
		bs1	    	
	| _ -> (match compile env e with
	    | Real (r,l,bs) -> r,l,bs
	    | _ -> error ("typecheck" ^ S.string_of_expr e))
  and
    compile_sigma env e bs0 = match e with
	| S.True -> ConstSigma true, []
	| S.False -> ConstSigma false, []
	| S.Less (e1, e2) -> 	    
	    let r1,l1,bs1 = compile_real env (S.Binary (S.Minus,e2,e1)) bs0 in	    
	    GtZero (r1,l1), bs1
	| S.And lst -> 
	    let r,bs,_ = List.fold_left (
		fun (rr,rbs,bs0) e -> 
		  let r,bs = compile_sigma env e bs0 in 
		  let bs0 = bs0 + List.length bs in
		    r::rr, bs@rbs, bs0) ([],[],bs0) lst in
	    And r, bs
	| S.Or lst -> 
	    let r,bs,_ = List.fold_left (
		fun (rr,rbs,bs0) e -> 
		  let r,bs = compile_sigma env e bs0 in 
		  let bs0 = bs0 + List.length bs in
		    r::rr, bs@rbs, bs0) ([],[],bs0) lst in
	    Or r, bs	    
	| S.Exists (x, i, e) -> 	    
	    let s,bs = compile_sigma (newenv env x) e 0 in
	    BsBVar bs0, [Exists ([i,1,bs],s)]
	| S.Forall (x, i, e) -> 
	    let s,bs = compile_sigma (newenv env x) e 0 in	    
	    BsBVar bs0, [Forall ([i,1,bs],s)]
	| _ -> (match compile env e with
	    | Sigma (s,bs) -> s,bs
	    | _ -> error ("typecheck" ^ S.string_of_expr e))           

 (** Convert an expression to string *)
  let rec string_of_expr e =
    match e with
	  | Real (r,l,bs) -> "real " ^ str_of_bs bs ^ " in (" ^ str_of_real r ^ "," ^ str_of_real l ^ ")"
	  | Sigma (s,bs) -> "sigma " ^ str_of_bs bs ^ " in " ^ str_of_sigma s 
	  | Tuple lst -> "(" ^ (String.concat ", " (List.map string_of_expr lst)) ^ ")"
	  | Uncompiled e -> "["^(S.string_of_expr e)^"]"
   and str_of_bs bs = "(" ^ String.concat ", " (List.map str_of_env bs) ^ ")"
   and str_of_ibs ibslst = "(" ^ String.concat ", " (List.map (fun (i,_,bs) -> I.to_string i ^ str_of_bs bs) ibslst) ^ ")"
   and str_of_env env = match env with
      | Forall (ibs, s) -> " forall: " ^ str_of_ibs ibs ^ " in " ^ str_of_sigma s
      | Exists (ibs, s) -> " exists: " ^ str_of_ibs ibs ^ " in " ^ str_of_sigma s
      | Cut (i, bs1, bs2,s1,s2) -> " cut: " ^ (I.to_string i) ^ 
	    " left " ^ str_of_bs bs1 ^ " in " ^ str_of_sigma s1 ^ 
	    " right " ^ str_of_bs bs2 ^ " in " ^ str_of_sigma s2
  and str_of_real r = match r with
    | EnvRVar i -> "x" ^ string_of_int i
    | EnvDRVar i -> "x" ^ string_of_int i ^ "'"
    | BsRVar i -> "y" ^ string_of_int i
    | Binary (op,r1,r2) -> (str_of_real r1) ^ "°" ^ (str_of_real r2)
    | Unary (_,r1) -> str_of_real r1    
    | ConstReal c -> I.to_string c
  and str_of_sigma s = match s with
    | BsBVar i -> "y"^string_of_int i
    | And lst -> String.concat "/\\" (List.map str_of_sigma lst)
    | Or lst -> String.concat "\\/" (List.map str_of_sigma lst)
    | GtZero (r,l) -> "0<(" ^ (str_of_real r) ^ "," ^ (str_of_real l) ^ ")"
    | ConstSigma c -> string_of_bool c

 (** Convert an expression to short string only giving basesets *)
let rec str_of_expr e =
    match e with
	  | Real (r,l,bs) -> str_of_bs bs 
	  | Sigma (s,bs) -> str_of_bs bs 
	  | Tuple lst -> "(" ^ (String.concat ", " (List.map string_of_expr lst)) ^ ")"
	  | Uncompiled e -> "["^(S.string_of_expr e)^"]"
   and str_of_bs bs = if List.length bs > 0 then  "(" ^ String.concat ", " (List.map str_of_env bs) ^ ")" else ""
   and str_of_ibs ibslst = if List.length ibslst > 0 then "(" ^ String.concat ", " (List.map (fun (i,sp,bs) -> I.to_string i ^ "/" ^ (string_of_int sp) ^ str_of_bs bs) ibslst) ^ ")"
      else ""
   and str_of_env env = match env with
      | Forall (ibs, s) -> str_of_ibs ibs 
      | Exists (ibs, s) -> str_of_ibs ibs 
      | Cut (i, bs1, bs2,s1,s2) -> (I.to_string i) ^ if List.length bs1 > 0 || List.length bs2 > 0 then
	    " left " ^ str_of_bs bs1 ^
	    " right " ^ str_of_bs bs2 else ""

end;;

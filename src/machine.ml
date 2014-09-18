module Make = functor (D : Dyadic.DYADIC) ->
struct
  module S = Syntax.Make(D)
  module I = Interval.Make(D)  
  module C = Compiler.Make(D)
  open C

  let lower_real ~prec ~round env bs r =
    let rec approx r =
	match r with 
	| EnvRVar i -> List.nth env i
	| EnvDRVar i -> error "not expecting a derivative"
	| BsRVar i -> (match (List.nth bs i) with
	    | Cut (i,_,_,_,_) -> i
	    | _ -> error "not a cut")
	| Binary (binaryop,r1,r2) -> binaryop ~prec ~round (approx r1) (approx r2)
	| Unary (unaryop,r) -> unaryop ~prec ~round (approx r)
	| ConstReal c -> c
    in approx r

  let upper_real ~prec ~round env bs r =
    let rec approx r =
	match r with 
	| EnvRVar i -> I.flip (List.nth env i)
	| EnvDRVar i -> error "not expecting a derivative"
	| BsRVar i -> (match (List.nth bs i) with
	    | Cut (i,_,_,_,_) -> I.flip i
	    | _ -> error "not a cut")
	| Binary (binaryop,r1,r2) -> binaryop ~prec ~round (approx r1) (approx r2)
	| Unary (unaryop,r) -> unaryop ~prec ~round (approx r)
	| ConstReal c -> I.flip c
    in approx r

  let rec split ~prec il =
    match il with
      | (i,sp,bs)::tail -> (List.map (fun i -> (i,bs)) (I.lsplit ~prec sp [i]))@(split ~prec tail)
      | [] -> []

  let rec lower ~prec env bs s =
    match s with 
    | BsBVar i -> (match (List.nth bs i) with
	| Exists (lst,s) -> let lst = split ~prec lst in
	  List.fold_left (||) false 
	    (List.rev_map (fun (i,bs) -> lower ~prec ((I.of_dyadic (I.midpoint prec 1 i))::env) bs s) lst)	    
	| Forall (lst,s) -> let lst = split ~prec lst in
	  List.fold_left (&&) true 
	    (List.rev_map (fun (i,bs) -> lower ~prec (i::env) bs s) lst)
	| _ -> error "not a sigma")
    | And lst -> List.fold_left (&&) true (List.rev_map (lower ~prec env bs) lst)
    | Or lst -> List.fold_left (||) false (List.rev_map (lower ~prec env bs) lst)
    | GtZero (r,l) -> 
	let i = lower_real ~prec ~round:D.down env bs r in        
                  D.positive (I.lower i) 
    | ConstSigma c -> c
 
  let rec upper ~prec env bs s =    
    match s with 
    | BsBVar i -> (match (List.nth bs i) with
	| Exists (lst,s) -> let lst = split ~prec lst in
	  List.fold_left (||) false 
	    (List.rev_map (fun (i,bs) -> upper ~prec ((i)::env) bs s) lst)	    
	| Forall (lst,s) -> let lst = split ~prec lst in
	  List.fold_left (&&) true 
	    (List.rev_map (fun (i,bs) -> upper ~prec ((I.of_dyadic (I.midpoint prec 1 i))::env) bs s) lst)
	| _ -> error "not a sigma")
    | And lst -> List.fold_left (&&) true (List.rev_map (upper ~prec env bs) lst)
    | Or  lst -> List.fold_left (||) false (List.rev_map (upper ~prec env bs) lst)
    | GtZero (r,l) -> 
	let i = upper_real ~prec ~round:D.up env bs r in D.positive (I.lower i)
    | ConstSigma c -> c

  exception Break of (I.t * int * basesets) list

  let rec refine ~k ~prec env bslist =
    let refine1 bs =
      match bs with
      | Exists (lst,s)->
	let qlst = try 
	  List.fold_left  (
	    fun restail (i,sp,bs)->
	      let prec = make_prec prec i in 
	      let q = refine ~k ~prec ((i)::env) bs in
	      let il = I.lsplit prec sp [i] in

	      let r = List.fold_left (fun r i -> 
		if (lower ~prec (i::env) q s) then raise (Break [(i,1,q)])
		else if upper ~prec (i::env) q s then i::r else r
		  ) [] il in	      
		match r with 
		  | [] -> restail
		  | [i] -> (i,sp+1,q) :: restail
		  | lst -> (List.map (fun i-> (i,1,q)) lst) @ restail	    	     
	   ) [] lst
	  with Break (qlst) -> qlst in Exists (qlst,s)
      | Forall (lst,s) ->   
	let qlst = try
	  List.fold_left  (
	    fun restail (i,sp,bs)->
	      let prec = make_prec prec i in 
	      let q = refine ~k ~prec ((i)::env) bs in
              let il = I.lsplit prec sp [i] in
              let r = List.fold_left (fun r i ->
		if lower ~prec ((i)::env) q s then r 
		else
		  (if upper ~prec ((i)::env) q s then i::r 
		  else raise (Break [(i,1,q)]))) [] il in
                  match r with
                   | [] -> restail
       		   | [i] -> (i,sp+1,q) :: restail
		   | lst -> (List.map (fun i-> (i,1,q)) lst) @ restail	    	     
	   ) [] lst
	  with Break(qlst)->qlst in
	    Forall (qlst,s)
      | Cut (i,bs1,bs2,s1,s2) ->
	  let prec = make_prec prec i in
	    (* To refine a cut [Cut(x,i,p1,p2)] we try to make the
		interval [i] smaller and refine [p1] and [p2]. *)
	  let a = I.lower i in
	  let b = I.upper i in
	    (* Bisection *)
	  let m1, m2 = I.thirds prec k i in
	  let a' = (if lower ~prec ((I.of_dyadic m1)::env) bs1 s1 then m1 else a) in
	  let b' = (if lower ~prec ((I.of_dyadic m2)::env) bs2 s2 then m2 else b) in
	  let j = I.make a' b' in       
	  let env' = (j)::env in
	  let q1 = refine ~k ~prec env' bs1 in
	  let q2 = refine ~k ~prec env' bs2 in
	  Cut (j,q1,q2,s1,s2)	  
    in List.map refine1 bslist

  let string_of_expr e =
    match e with
    | Real (r,l,bs) -> 
	let i = lower_real ~prec:32 ~round:D.down [] bs r in 
	  I.to_string_number i
    | Sigma (s,bs) -> string_of_bool (lower ~prec:32 [] bs s) 
    | Tuple lst -> "(" ^ (String.concat ", " (List.map string_of_expr lst)) ^ ")"      
    | Uncompiled e -> "["^(S.string_of_expr e)^"]"

  let target_precision = ref (D.make_int ~prec:10 ~round:D.up 1 (-52))

  let exec trace e =  
    let rec loop k p e' =
      if trace then
        begin
          print_endline ("--------------------------------------------------\n" ^
                           "Iteration: " ^ string_of_int k ^ "\n" ^
                           C.string_of_expr e' ^ "\n" ^
                           "Press Enter to continue " 
                        ) ;
          ignore (read_line ())   
        end ;
      match e' with
        | Real (r,l,bs) ->
            let i = lower_real ~prec:p ~round:D.down [] bs r in
            let w = (I.width 10 D.up i) in          
              if D.lt w !target_precision then
                (e', Real (r,l,bs))
              else
                loop (k+1) (make_prec (p+3) (I.make D.zero !target_precision)) (Real (r,l,refine ~k ~prec:p [] bs))
        | Sigma (s,bs) ->
          if (lower ~prec:p [] bs s) then (e', Sigma (s,bs))
          else 
            (if (upper ~prec:p [] bs s) then
              loop (k+1) (p+1) (Sigma (s,refine ~k ~prec:p [] bs))
            else (e', Sigma (s,bs)))
        |  _ -> (e', e')
    in            
      loop 1 32 e  

end;;

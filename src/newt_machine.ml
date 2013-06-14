module Make = functor (D : Dyadic.DYADIC) ->
struct
  module S = Syntax.Make(D)
  module I = Interval.Make(D)  
  module C = Compiler.Make(D)
  module R = Region.Make(D)
  open C

  let dummy = -1

  let lower_real ~prec ~round y env bs r =
    let rec approx r =
	match r with 
	| EnvRVar x -> List.nth env x
	| EnvDRVar x -> if x == y then I.of_dyadic D.one else I.of_dyadic D.zero
	| BsRVar x -> (match (List.nth bs x) with
	    | Cut (i,_,_,_,_) -> i
	    | _ -> error "not a cut")
	| Binary (binaryop,r1,r2) -> binaryop ~prec ~round (approx r1) (approx r2)
	| Unary (unaryop,r) -> unaryop ~prec ~round (approx r)
	| ConstReal c -> c
    in approx r

  let upper_real ~prec ~round y env bs r =
    let rec approx r =
	match r with 
	| EnvRVar x -> I.flip (List.nth env x)
	| EnvDRVar x -> if x == y then I.of_dyadic D.one else I.of_dyadic D.zero
	| BsRVar x -> (match (List.nth bs x) with
	    | Cut (i,_,_,_,_) -> I.flip i
	    | _ -> error "not a cut")
	| Binary (binaryop,r1,r2) -> binaryop ~prec ~round (approx r1) (approx r2)
	| Unary (unaryop,r) -> unaryop ~prec ~round (approx r)
	| ConstReal c -> I.flip c
    in approx r

  let estimate_endpoint prec x y d =            
        match D.sgn d with
  	| `negative ->
  	    let b' = D.sub ~prec ~round:D.down x (D.div ~prec ~round:D.up y d) in  	      
  		R.open_left_ray b'
  	| `zero ->
  	    (match D.sgn y with
  	       | `negative | `zero -> R.empty
  	       | `positive -> R.real_line)
  	| `positive ->
  	    let a' = D.sub ~prec ~round:D.up x (D.div ~prec ~round:D.down y d) in  	     
  		R.open_right_ray a'

  let getx x env =
    if x<0 then I.bottom else List.nth env x    

  let gety y env = R.of_interval (getx y env)

  let rec putenv i xi env =
    match xi,env with
      | 0,hd::tl -> i::tl 
      | _,hd::tl -> hd::(putenv i (xi-1) tl)
      | _,[] -> error "putenv"

  let lower_gtzero ~prec x env bs e l =
    (* For infinite intervals we give up. We could try to do something
       more intelligent, such as computing the derivative at infinity
       (using a suitable transformation which moves infinity to a finite
       point). *)
      (*let i = lower_real ~prec ~round:D.down x env bs e in        
                 if D.positive (I.lower i) then (gety x env) else R.empty*)
    let i = getx x env in
    let old_est () = 
		 (let j = lower_real ~prec ~round:D.down x env bs e in        
                   if D.positive (I.lower j) then R.of_interval i else R.empty) in
    if not (I.proper i) then
      old_est ()
    else      
      let x1 = I.lower i in
      let x2 = I.upper i in
      let y1 = I.lower (lower_real ~prec ~round:D.down x (putenv (I.of_dyadic x1) x env) bs e) in 
      let y2 = I.lower (lower_real ~prec ~round:D.down x (putenv (I.of_dyadic x2) x env) bs e) in 
      let lif = lower_real ~prec ~round:D.down x (putenv i x env) bs l in  (* Lifschitz constant as an interval *)      	
	if not (I.proper lif) then old_est () else
	R.intersection (R.of_interval i) (R.union
	  (estimate_endpoint prec x1 y1 (I.lower lif)) (* estimate at i.lower *)
	  (estimate_endpoint prec x2 y2 (I.upper lif)))  


  let upper_gtzero ~prec x env bs e l =
    (* For infinite intervals we give up. We could try to do something
       more intelligent, such as computing the derivative at infinity
       (using a suitable transformation which moves infinity to a finite
       point). *)
(*    let i = upper_real ~prec ~round:D.up x env bs e in        
                  if D.positive (I.lower i) then gety x env else R.empty*)
    let i = getx x env in
    let old_est () = (let j = upper_real ~prec ~round:D.up x env bs e in        
                  if D.positive (I.lower j) then R.of_interval i else R.empty) in
    if not (I.proper i) then
      old_est ()
    else      
      let x1 = I.lower i in
      let x2 = I.upper i in
      let y1 = I.lower (upper_real ~prec ~round:D.down x (putenv (I.of_dyadic x1) x env) bs e) in 
      let y2 = I.lower (upper_real ~prec ~round:D.down x (putenv (I.of_dyadic x2) x env) bs e) in 
      let lif = upper_real ~prec ~round:D.down x (putenv i x env) bs l in  (* Lifschitz constant as an interval *)                       
	if not (I.proper (I.flip lif)) then old_est () else
	  R.intersection (R.of_interval i) (R.union (estimate_endpoint prec x1 y1 (I.lower lif))
		 (estimate_endpoint prec x2 y2 (I.upper lif)))

  let rec lower ~prec y env bs s =
    match s with 
    | BsBVar x -> (match (List.nth bs x) with
	| Exists (lst,s) -> 
	  List.fold_left (R.union) R.empty 
	    (List.rev_map (fun (i,bs) -> lower ~prec (y+1) ((I.of_dyadic (I.midpoint prec 1 i))::env) bs s) lst)	    
	| Forall (lst,s) ->
	  List.fold_left (R.intersection) (gety y env)
	    (List.rev_map (fun (i,bs) -> lower ~prec (y+1) ((i)::env) bs s) lst)
	| _ -> error "not a sigma")
    | And lst -> List.fold_left (R.intersection) (gety y env) (List.rev_map (lower ~prec y env bs) lst)
    | Or lst -> List.fold_left (R.union) R.empty (List.rev_map (lower ~prec y env bs) lst)
    | GtZero (r,l) -> 
	lower_gtzero ~prec y env bs r l	
    | ConstSigma c -> if c then gety y env else R.empty
 
  let rec upper ~prec y env bs s =    
    match s with 
    | BsBVar x -> (match (List.nth bs x) with
	| Exists (lst,s) -> 
	  List.fold_left (R.union) R.empty
	    (List.rev_map (fun (i,bs) -> upper ~prec (y+1) ((i)::env) bs s) lst)	    
	| Forall (lst,s) ->
	  List.fold_left (R.intersection) (gety y env) 
	    (List.rev_map (fun (i,bs) -> upper ~prec (y+1) ((I.of_dyadic (I.midpoint prec 1 i))::env) bs s) lst)
	| _ -> error "not a sigma")
    | And lst -> List.fold_left (R.intersection) (gety y env) (List.rev_map (upper ~prec y env bs) lst)
    | Or  lst -> List.fold_left (R.union) R.empty (List.rev_map (upper ~prec y env bs) lst)
    | GtZero (r,l) ->
	upper_gtzero ~prec y env bs r l	
    | ConstSigma c -> if c then gety y env else R.empty


  exception Break of (I.t * basesets) list

  let comp i r = R.intersection (R.of_interval i) (R.complement r)

  let rec refine ~k ~prec env bslist =
    let refine1 bs =
      match bs with
      | Exists (lst,s)->
	let qlst = try
	  List.fold_left  (
	    fun restail (i,bs)->
	      let prec = make_prec prec i in 
	      let q = refine ~k ~prec ((i)::env) bs in
	      let i1, i2 = I.split prec 1 i in
		if R.is_inhabited (lower ~prec 0 ((i1)::env) q s) then raise (Break [(i1,q)]) 
		else
		  if R.is_inhabited (lower ~prec 0 ((i2)::env) q s) then raise (Break [(i2,q)]) 
		  else
		    let lst1 = R.to_closed_intervals (R.closure (upper ~prec 0 ((i1)::env) q s)) in
		    let lst2 = R.to_closed_intervals (R.closure (upper ~prec 0 ((i2)::env) q s)) in
		      (List.map (fun i -> (i,q)) (lst1@lst2))@restail		    	      
	      ) [] lst 
	  with Break (qlst) -> qlst in
         Exists (qlst,s)
      | Forall (lst,s) ->   	
	let qlst = try 	
	  List.fold_left  (
	    fun restail (i,bs)->
	      let prec = make_prec prec i in 
	      let q = refine ~k ~prec ((i)::env) bs in
	      let i1, i2 = I.split prec 1 i in
		if R.is_inhabited (comp i1 (upper ~prec 0 ((i1)::env) q s)) then raise (Break [(i1,q)])
		else
		  if R.is_inhabited (comp i2 (upper ~prec 0 ((i2)::env) q s)) then raise (Break [(i2,q)])
		  else		  
		      let lst1 = R.to_closed_intervals (R.closure (comp i1 (lower ~prec 0 ((i1)::env) q s))) in
		      let lst2 = R.to_closed_intervals (R.closure (comp i2 (lower ~prec 0 ((i2)::env) q s))) in
			(List.map (fun i -> (i,q)) (lst1@lst2))@restail		   		  
	    ) [] lst
	  with Break (qlst) -> qlst in
                    Forall (qlst,s)
      | Cut (i,bs1,bs2,s1,s2) ->
	  let prec = make_prec prec i in
	    (* To refine a cut [Cut(x,i,p1,p2)] we try to make the
		interval [i] smaller and refine [p1] and [p2]. *)
	  let a = I.lower i in
	  let b = I.upper i in
	    (* Bisection *)
	  let m1, m2 = I.thirds prec k i in
	  let a' = (if R.is_inhabited (lower ~prec dummy ((I.of_dyadic m1)::env) bs1 s1) then m1 else a) in
	  let b' = (if R.is_inhabited (lower ~prec dummy ((I.of_dyadic m2)::env) bs2 s2) then m2 else b) in
	  let j = I.make a' b' in       
	     
	  (* Newton's method *)
	  let l1 = lower ~prec 0 ((j)::env) bs1 s1 in
	  let u1 = comp j (upper ~prec 0 ((j)::env) bs1 s1) in	  
	  let l2 = lower ~prec 0 ((j)::env) bs2 s2 in  	  
	  let u2 = comp j (upper ~prec 0 ((j)::env) bs2 s2) in
  
	  let a'' = D.max a' (D.max (R.supremum l1) (R.supremum u2)) in
	  let b'' = D.min b' (D.min (R.infimum  l2) (R.infimum u1)) in
	  let l = I.make a'' b'' in	      	    
	      (match D.cmp a'' b'' with
		  | `less ->
		      (* The new interval *)		    
		    let env' = (l)::env in
		    let q1 = refine ~k ~prec env' bs1 in
		    let q2 = refine ~k ~prec env' bs2 in
(*		    print_endline ("Cut: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (I.to_string j) ^ (I.to_string l) ^ (S.string_of_expr q1) ^ (S.string_of_expr q2));*)
		      Cut (l, q1, q2, s1, s2)
		  | `equal ->
		      (* We found an exact value *)
		      Cut (l, bs1, bs2, s1, s2)
		  | `greater ->
		      (* We have a backwards cut. Do nothing. Someone should think
			 whether this is ok. It would be nice if cuts could be
			 overlapping, but I have not thought whether this would break
			 anything else.
		      *)
		      bs)
	      
	  (*let env' = (x,j)::env in
	  let q1 = refine ~k ~prec env' bs1 in
	  let q2 = refine ~k ~prec env' bs2 in
	  Cut (x,j,q1,q2,s1,s2)	  *)
    in List.map refine1 bslist

  let string_of_expr e =
    match e with
    | Real (r,l,bs) -> 
	let i = lower_real ~prec:32 ~round:D.down dummy [] bs r in 
	  I.to_string_number i
    | Sigma (s,bs) -> string_of_bool (R.is_inhabited (lower ~prec:32 dummy [] bs s))
    | Tuple lst -> "(" ^ (String.concat ", " (List.map string_of_expr lst)) ^ ")"      
    | Uncompiled e -> "["^(S.string_of_expr e)^"]"

  let target_precision = ref (D.make_int ~prec:10 ~round:D.up 1 (-53))

  let exec trace e =  
    let rec loop k p e' =
      if trace then
        begin
          print_endline ("--------------------------------------------------\n" ^
                           "Iteration: " ^ string_of_int k ^ "\n" ^
                           C.str_of_expr e' ^ "\n" ^
                           "Press Enter to continue " 
                        ) ;
          ignore (read_line ())   
        end ;
      match e' with
        | Real (r,l,bs) ->
            let i = lower_real ~prec:p ~round:D.down dummy [] bs r in
            let w = (I.width 10 D.up i) in          
              if D.lt w !target_precision then
                (e', Real (r,l,bs))
              else
                loop (k+1) (make_prec (p+3) (I.make D.zero !target_precision)) (Real (r,l,refine ~k ~prec:p [] bs))
        | Sigma (s,bs) ->
          if R.is_inhabited (lower ~prec:p dummy [] bs s) then (e', Sigma (s,bs))
          else 
            (if R.is_inhabited (upper ~prec:p dummy [] bs s) then
              loop (k+1) (p+1) (Sigma (s,refine ~k ~prec:p [] bs))
            else (e', Sigma (s,bs)))
        |  _ -> (e', e')
    in            
      loop 1 32 e  

end;;

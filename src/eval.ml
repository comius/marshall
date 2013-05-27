module Make = functor (D : Dyadic.DYADIC) ->
struct

  module I = Interval.Make(D)
  module Env = Environment.Make(D)
  module N = Newton.Make(D)
  module R = Region.Make(D)
  module A = Approximate.Make(D)
  module T = Types.Make(D)

  let error = Message.runtime_error

  (* The target precision for top-level evaluation of real
     numbers. Default is 53 bits, like floating-point. *)

  let target_precision = ref (D.make_int ~prec:10 ~round:D.up 1 (-53))

  (* Given precision [prec] and interval [i], compute a precision which
     is better than [prec] and is suitable for working with intervals of
     width [i]. *)

  let make_prec prec i =
    let w = I.width ~prec:2 ~round:D.up i in
    let e1 = D.get_exp w in
    let e2 = max (D.get_exp (I.lower i)) (D.get_exp (I.upper i)) in
      max 2 (max prec (- 5 * (e1 - e2) / 4))

  (* [make_exists x i p] constructs the existential quantifier [Exists (x,i,p)]
     over an inhabited interval [i]. If [p] is [True] or [False] it shortcircuits
     the quantifier. *)

  let make_exists x i p =
    assert (I.forward i) ;
    if p = T.True then
      T.True
    else if p = T.False then
      T.False
    else
      T.Exists (x, i, p)

  (* [make_forall x i p] constructs the universal quantifier [Forall (x,i,p)]
     over an inhabited interval [i]. If [p] is [True] or [False] it shortcircuits
     the quantifier. *)

  let make_forall x i p =
    assert (I.forward i) ;
    if p = T.True then
      T.True
    else if p = T.False then
      T.False
    else
      T.Forall (x, i, p)


  (* \subsection{Evaluation} *)

  (* The function [refine k prec env e] performs one step of evaluation
     of expression [e] in environment [env], using precision [prec] to
     compute arithmetical expressions. This is used by [eval] below to
     make progress.  The counter [k] tells which successive refinement
     this is.

     We need to be able to refine expressions which contain free
     variables (in order to refine cuts and quantifiers). For this
     purpose we have a special expression [RealVar (x,i)] which denotes
     free variable [x] ranging over interval [i].
  *)

  let rec refine k prec env e =
    let refn = refine k prec env in
      if A.lower prec env e = T.True then T.True
      else if A.upper prec env e = T.False then T.False
      else
	match e with
	  | T.True -> T.True
	  | T.False -> T.False
	  | T.Less (e1, e2) -> T.Less (refinea k prec env  e1, refinea k prec env e2)
	  | T.And lst -> A.fold_and refn lst
	  | T.Or lst -> A.fold_or refn lst
	  | T.Exists (x, i, p) ->
	      let prec = make_prec prec i in
	      let q = refine k prec (Env.extend x (T.RealVar (x, i)) env) p in
	    (*  let (a1,b1) = N.estimate k prec env x i q in
              if R.is_inhabited b1 then S.True
              else
                (if R.is_inhabited a1 then
                  let lst = R.to_closed_intervals (R.closure (R.intersection (R.of_interval i) (R.complement a1))) in
		      A.fold_or (fun i -> make_exists x i q) lst
                else
		  let i1,i2 = I.split prec 1 i in  
	              A.fold_or (fun i -> make_exists x i q) [i1; i2])*)
	      let i1, i2 = I.split prec 1 i in
		(* Newton's method *)
	      let (a1, b1) = N.estimate k prec env x i1 q in

(*	      print_endline ("Exists: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a1) ^ (R.to_string b1));*)
	      if R.is_inhabited b1 then
		(* We could collect [b1] as a witness here. *)
		T.True
	      else
		let (a2, b2) = N.estimate k prec env x i2 q in
(*		  print_endline ("Exists: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a2) ^ (R.to_string b2));*)
		  if R.is_inhabited b2 then
		    (* We could collect [b2] as a witness here. *)
		    T.True
		  else
		    let lst1 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i1)
			    (R.complement a1)))
		    in
		    let lst2 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i2)
			    (R.complement a2)))
		    in
		      A.fold_or (fun i -> make_exists x i q) (lst1 @ lst2)
		
	      (*A.fold_or (fun i -> make_exists x i q) [i1; i2]*)

	  | T.Forall (x, i, p) ->
	      let prec = make_prec prec i in
	      let q = refine k prec (Env.extend x (T.RealVar (x, i)) env) p in
(*      let (a1, b1) = N.estimate k prec env x i q in
	      if R.is_inhabited a1 then
		(* We could take [a1] as witness for quantifier being false. *)
		S.False
	      else
                (if R.is_inhabited b1 then
 		    let lst = R.to_closed_intervals (R.closure (R.intersection (R.of_interval i) (R.complement b1))) in
		      A.fold_and (fun i -> make_forall x i q) lst
		else
	       	  let i1, i2 = I.split prec 1 i in
              	    A.fold_and (fun i -> make_forall x i q) [i1; i2])*)
	      
	       let i1, i2 = I.split prec 1 i in

		(* Newton's method *)
              let (a1, b1) = N.estimate k prec env x i1 q in
(*	      print_endline ("Forall: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a1) ^ (R.to_string b1));*)
	      if R.is_inhabited a1 then
		(* We could take [a1] as witness for quantifier being false. *)
		T.False
	      else
		let (a2, b2) = N.estimate k prec env x i2 q in
(*		print_endline ("Forall: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a2) ^ (R.to_string b2));*)
		  if R.is_inhabited a2 then
		    (* We could take [a2] as witness for quantifier being false. *)
		    T.False
		  else
		    let lst1 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i1)
			    (R.complement b1)))
		    in
		    let lst2 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i2)
			    (R.complement b2)))
		    in
		      A.fold_and (fun i -> make_forall x i q) (lst1 @lst2)

              (*A.fold_and (fun i -> make_forall x i q) [i1; i2]	  *)
	  
	and
  refinea k prec env e =
    let refn = refinea k prec env in
	match e with
	  | T.Binary (op, e1, e2) -> T.Binary (op, refn e1, refn e2)
	  | T.Unary (op, e) -> T.Unary (op, refn e)
	  | T.Power (e, k) -> T.Power (refn e, k)
	  | T.Var x -> refinea k prec env (Env.get x env)
	  | T.RealVar (x, _) -> T.Var x
	  | T.Dyadic _ -> e
	  | T.Interval _ -> e
	  | T.Cut (x, i, p1, p2) -> begin
	      let prec = make_prec prec i in
		(* To refine a cut [Cut(x,i,p1,p2)] we try to make the
		   interval [i] smaller and refine [p1] and [p2]. *)
	      let a = I.lower i in
	      let b = I.upper i in
		(* Bisection *)
	      let m1, m2 = I.thirds prec k i in
	      let a' = (if A.lower prec (Env.extend x (T.Dyadic m1) env) p1 = T.True then m1 else a) in
	      let b' = (if A.lower prec (Env.extend x (T.Dyadic m2) env) p2 = T.True then m2 else b) in


	      let j = I.make a' b' in 

	      	(* Newton's method *)
	      let (r1, r2) = N.estimate k prec env x j p1 in
	      let (s1, s2) = N.estimate k prec env x j p2 in
      	      let a'' = D.max a' (D.max (R.supremum r2) (R.supremum s1)) in
	      let b'' = D.min b' (D.min (R.infimum  s2) (R.infimum r1)) in
	      match D.cmp a'' b'' with
		  | `less ->
		      (* The new interval *)
		    let l = I.make a'' b'' in	      	    
		    let env' = Env.extend x (T.RealVar (x, l)) env in
		    let q1 = refine k prec env' p1 in
		    let q2 = refine k prec env' p2 in
(*		    print_endline ("Cut: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (I.to_string j) ^ (I.to_string l) ^ (S.string_of_expr q1) ^ (S.string_of_expr q2));*)
		      T.Cut (x, l, q1, q2)
		  | `equal ->
		      (* We found an exact value *)
		    T.Dyadic a'
		  | `greater ->
		      (* We have a backwards cut. Do nothing. Someone should think
			 whether this is ok. It would be nice if cuts could be
			 overlapping, but I have not thought whether this would break
			 anything else.
		      *)
		    e
	    end
	  
  (** [eval prec env e] evaluates expression [e] in environment [env] by
      repeatedly calling [refine]. It increases precision at each step,
      although we should do something more intelligent about that (not
      all subexpressions of [e] need the same precision). The argument
      [trace] determines whether debugging information should be printed
      out. *)
  let eval trace e =  
    let rec loop k p e' =
      if trace then
	begin
	  print_endline ("--------------------------------------------------\n" ^
			   "Iteration: " ^ string_of_int k ^ "\n" ^
			   T.string_of_expr e' ^ "\n" ^
			   "Press Enter to continue " 
			) ;
	  ignore (read_line ())	  
	end ;
      match e' with
	| T.Sigma T.True | T.Sigma T.False -> (e',e')
	| T.Sigma s -> loop (k+1) (p+1) (T.Sigma (refine k p [] s))
	| T.Real r ->
	    let i = A.lowera p [] r in	       
	    let w = (I.width 10 D.up i) in
	      if D.lt w !target_precision then
		(e', T.Real (T.Interval i))
	      else
		loop (k+1) (make_prec (p+3) (I.make D.zero !target_precision)) (T.Real (refinea k p [] r))	
	| T.Tuple lst -> 
	    let lst1, lst2 =
	      List.fold_left
		(fun (lst1, lst2) e ->
		   let v1, v2 = loop k p e in
		     v1::lst1, v2::lst2)
		([], [])
		lst
	    in
	      (T.Tuple lst1, T.Tuple lst2)
	| T.Unconverted _ -> (e', e')
    in            
      loop 1 32 e
end;;


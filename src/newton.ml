module Make = functor (D : Dyadic.DYADIC) ->
struct

  module I = Interval.Make(D)
  module T = Types.Make(D)
  module S = Syntax.Make(D)
  module R = Region.Make(D)
  module A = Approximate.Make(D)
  module Env = Environment.Make(D)

  (* \subsection{Newton's method} *)
 
  (* This section is not finished because we have to sort out problems which
     are caused by appearance of back-to-front intervals. *)
  
   (* Does [x] occur freely in [e]? *)
   let rec frees x = function
     | T.True
     | T.False -> true
     | T.Less (e1, e2) -> free x e1 && free x e2
     | T.And lst
     | T.Or lst -> List.for_all (frees x) lst
     | T.Exists (y, _, e)
     | T.Forall (y, _, e) -> x = y || frees x e
  and 
  (* Does [x] occur freely in [e]? *)
  free x = function
    | T.Var y -> x <> y
    | T.RealVar (y, _) -> x <> y
    | T.Dyadic _
    | T.Interval _ -> true
    | T.Cut (y, _, p1, p2) -> x = y || (frees x p1 && frees x p2)
    | T.Binary (_, e1, e2) -> free x e1 && free x e2   
    | T.Unary (_, e)
    | T.Power (e, _) -> free x e    
    
  (* Suppose [e] is an expression in environment [env] with a free
     variable [x]. Then [e] as a function of [x] maps a real [x] to an
     interval $[e_1(x), e_2(x)]$.
  
     For estimation of inequalities we need to compute upper and lower
     Lipschitz constants for $e_1(x)$ when $x$ ranges over a given
     interval. This we do by symbolic differentiation.
  
     We assume that the expressions are in head
     normal form and of type real. In particular, this means we are
     never going to see a lambda abstraction, a tuple, a projection, or
     a local definition.
  *)
  
  let zero = T.Dyadic D.zero
  let one = T.Dyadic D.one
  
  let rec diff x = function
    | T.Var y -> if x = y then one else zero
    | T.RealVar (y, _) -> if x = y then one else zero
    | T.Dyadic _ -> zero
    | T.Interval _ -> zero
    | T.Cut (y, i, p1, p2) -> 
        if x = y || (frees x p1 && frees x p2) then
  	zero
        else
  	T.Interval I.bottom
    | T.Binary (S.Plus, e1, e2) -> T.Binary (S.Plus, diff x e1, diff x e2)
    | T.Binary (S.Minus, e1, e2) -> T.Binary (S.Minus, diff x e1, diff x e2)
    | T.Binary (S.Times, e1, e2) -> 
        T.Binary (S.Plus,
  	      T.Binary (S.Times, diff x e1, e2),
  	      T.Binary (S.Times, e1, diff x e2))
    | T.Binary (S.Quotient, e1, e2) ->
        T.Binary (S.Quotient,
  	      T.Binary (S.Minus,
  		      T.Binary (S.Times, diff x e1, e2),
  		      T.Binary (S.Times, e1, diff x e2)),
  	      T.Power (e2, 2))
    | T.Unary (S.Opposite, e) -> T.Unary (S.Opposite, diff x e)
    | T.Unary (S.Inverse, e) -> T.Binary (S.Quotient, diff x e, T.Power (e, 2))
    (*| S.Unary (S.Exp, e) -> S.Binary (S.Times, S.Unary (S.Exp, e), diff x e)*)
    | T.Power (e, 0) -> zero
    | T.Power (e, 1) -> diff x e
    | T.Power (e, k) ->
        T.Binary (S.Times,
  	      T.Dyadic (D.of_int ~round:D.down k),
  	      T.Binary (S.Times,
  		      T.Power (e, k-1),
  		      diff x e))    
  
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

  (* The function [estimate_positive env x i e] returns a set such that
     in environment [env] the expression [e] with free variable [x]
     ranging over interval [i] we have [0 < e] everywhere on the set. It
     uses interval Newton's method.
  *)

  let estimate_positive prec env x i e =
    (* For infinite intervals we give up. We could try to do something
       more intelligent, such as computing the derivative at infinity
       (using a suitable transformation which moves infinity to a finite
       point). *)
    if not (I.proper i) then
      R.empty
    else
      let x1 = I.lower i in
      let x2 = I.upper i in
      let y1 = I.lower (A.lowera prec (Env.extend x (T.Dyadic x1) env) e) in 
      let y2 = I.lower (A.lowera prec (Env.extend x (T.Dyadic x2) env) e) in 
      let lif = A.lowera prec (Env.extend x (T.Interval i) env) (diff x e) in  (* Lifschitz constant as an interval *)      	
	(R.union
	  (estimate_endpoint prec x1 y1 (I.lower lif)) (* estimate at i.lower *)
	  (estimate_endpoint prec x2 y2 (I.upper lif)))  (* estimate at i.upper*)

  (* The function [estimate_non_positive env x i e] returns a
     set such that in environment [env] the expression [e] with
     free variable [x] ranging over interval [i] is guaranteed to be
     non-positive everywhere on the complement of the set.
  *)
  
  let estimate_non_positive k prec env x i e =
    (* For infinite intervals we give up. We could try to do something
       more intelligent, such as computing the derivative at infinity
       (using a suitable transformation which moves infinity to a finite
       point). *)
    if not (I.proper i) then
      R.real_line
    else
      let x1 = I.lower i in
      let x2 = I.upper i in
      let y1 = I.lower (A.uppera prec (Env.extend x (T.Dyadic x1) env) e) in 
      let y2 = I.lower (A.uppera prec (Env.extend x (T.Dyadic x2) env) e) in 
      let lif = A.uppera prec (Env.extend x (T.Interval (I.flip i)) env) (diff x e) in  (* Lifschitz constant as an interval *)                 
      if not (I.proper (I.flip lif)) then R.real_line else
	  R.union (estimate_endpoint prec x1 y1 (I.lower lif))
		 (estimate_endpoint prec x2 y2 (I.upper lif))
	

  (* The function [estimate prec env i x p] returns a pair of sets [(a,b)]
     such that in environment [env] the proposition [p] with free
     variable [x] ranging over interval [i] fails everywhere on [a] and
     holds everywhere on [b].
  *)
  
  let rec estimate_true k prec env x i = function
    | T.True -> R.real_line
    | T.False -> R.empty
    | T.And lst ->
        List.fold_left
  	(fun r p -> R.intersection r (estimate_true k prec env x i p))
  	R.real_line
  	lst
    | T.Or lst ->
        List.fold_left
  	(fun r p -> R.union r (estimate_true k prec env x i p))
  	R.empty
  	lst
    | T.Less (e1, e2) -> estimate_positive prec env x i (T.Binary (S.Minus, e2, e1))
    | T.Exists (y, j, p) ->
        estimate_true k prec (Env.extend y (T.Dyadic (I.midpoint prec k j)) env) x i p
    | T.Forall (y, j, p) ->
        estimate_true k prec (Env.extend y (T.Interval j) env) x i p    
  
  let rec estimate_false k prec env x i = function
    | T.True -> R.real_line
    | T.False -> R.empty
    | T.And lst ->
        List.fold_left
  	(fun r p -> R.intersection r (estimate_false k prec env x i p))
  	R.real_line
  	lst
    | T.Or lst ->
        List.fold_left
  	(fun r p -> R.union r (estimate_false k prec env x i p))
  	R.empty
  	lst
   (* | S.Less (e1, e2) -> estimate_non_positive prec env x i (S.Binary (S.Minus, e2, e1))*)
    | T.Less (e1, e2) ->
       let r = estimate_non_positive k prec env x i (T.Binary (S.Minus, e2, e1)) in
   (*    print_endline ("Estimated " ^ S.string_of_name x ^ " on " ^ I.to_string i ^ " with " ^ Env.string_of_env env ^ " | " ^ S.string_of_expr (S.Less (e1, e2)) ^ " to be false on " ^ R.to_string r ^ "\n");*)
	r
    | T.Exists (y, j, p) ->
        estimate_false k prec (Env.extend y (T.Interval (I.flip j)) env) x i p
    | T.Forall (y, j, p) ->
        estimate_false k prec (Env.extend y (T.Dyadic (I.midpoint prec k j)) env) x i p    
  
  let estimate k prec env x i p =
    (R.intersection (R.complement (estimate_false k prec env x i p)) (R.of_interval i),
     R.intersection (estimate_true k prec env x i p)  (R.of_interval i))
  
end;;
 

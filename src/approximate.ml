module Make = functor (D : Dyadic.DYADIC) ->
struct

  module I = Interval.Make(D)
  module Env = Environment.Make(D)  
  module T = Types.Make(D)
  module S = Syntax.Make(D)  

  (* Apply a binary artithmetical operator with precision [prec]. The
     rounding mode, which is [Dyadic.down] or [Dyadic.up] tells whether
     we want a lower or an upper approximant. *)

  let bin_apply ~prec ~round op i1 i2 =
    match op with
      | S.Plus -> I.add ~prec ~round i1 i2
      | S.Minus -> I.sub ~prec ~round i1 i2
      | S.Times -> I.mul ~prec ~round i1 i2
      | S.Quotient -> I.div ~prec ~round i1 i2

  (* Apply a unary operator, see [bin_apply] for explanation of [prec]
     and [round]. *)

  let unary_apply ~prec ~round op i =
    match op with
      | S.Opposite -> I.neg ~prec ~round i
      | S.Inverse -> I.inv ~prec ~round i
	  (*| S.Exp -> I.exp ~prec ~round i*)

  (* [Break] is used to shortcircuit evaluation of conjunctions and
     disjunctions. *)

  exception Break

  (* [fold_and f [x1,...,xn]] constructs the conjunction [And [f x1;
     ..., f xn]]. It throws out [True]'s and shortcircuits on
     [False]. *)

  let fold_and f lst =
    let rec fold acc = function
      | [] -> acc
      | p::ps ->
	  (match f p with
	     | T.True -> fold acc ps
	     | T.False -> raise Break
	     | q -> fold (q::acc) ps)
    in
      try
	match fold [] lst with
	  | [] -> T.True
	  | lst -> T.And (List.rev lst)
      with Break -> T.False

  (* [fold_or f [x1,...,xn]] constructs the disjunction [Or [f x1;
     ..., f xn]]. It throws out [False]'s and shortcircuits on
     [True]. *)

  let fold_or f lst =
    let rec fold acc = function
      | [] -> acc
      | p::ps ->
	  (match f p with
	     | T.True -> raise Break
	     | T.False -> fold acc ps
	     | q -> fold (q::acc) ps)
    in
      try
	match fold [] lst with
	  | [] -> T.False
	  | lst -> T.Or (List.rev lst)
      with Break -> T.True


  (* \subsection{Approximants} *)

  (* [lower prec env e] computes the lower approximant of [e] in
     environment [env], computing arithmetical expressions with precision
     [prec]. *)

  let rec lower prec env e =
    let approx = lower prec env in
      match e with	
	| T.True -> T.True
	| T.False -> T.False
	| T.Less (e1, e2) ->
	    let i1 = lowera prec env e1 in
	    let i2 = lowera prec env e2 in
	      if D.lt (I.upper i1) (I.lower i2) then
		T.True
	      else
		T.False
	| T.And lst -> fold_and approx lst
	| T.Or lst -> fold_or approx lst
	| T.Exists (x, s, e) ->
	    let m = T.Dyadic (I.midpoint prec 1 s) in
	      lower prec (Env.extend x m env) e
	| T.Forall (x, i, e) ->
	    lower prec (Env.extend x (T.Interval i) env) e	
  and
  lowera prec env e =
    let approx = lowera prec env in
      match e with
	| T.Var x -> approx (Env.get x env)
	| T.RealVar (_, i) -> i
	| T.Dyadic q -> I.of_dyadic q
	| T.Interval i -> i
	| T.Cut (_, i, _, _) -> i
	| T.Binary (op, e1, e2) ->
	    let i1 = approx e1 in
	    let i2 = approx e2 in
	      bin_apply ~prec ~round:D.down op i1 i2
	| T.Unary (op, e) ->
	    let i = approx e in
	      unary_apply ~prec ~round:D.down op i
	| T.Power (e, k) ->
	    let i = approx e in
	      I.pow ~prec ~round:D.down i k

  (* Function [upper prec env e] computes the upper approximant of [e]
     in environment [env], computing arithmetical expressions with
     precision [prec]. *)

  let rec upper prec env e =
    let approx = upper prec env in
      match e with	
	| T.True -> T.True
	| T.False -> T.False
	| T.Less (e1, e2) ->
	    let i1 = uppera prec env e1 in
	    let i2 = uppera prec env e2 in
	      if D.lt (I.upper i1) (I.lower i2) then
		T.True
	      else
		T.False
	| T.And lst -> fold_and approx lst
	| T.Or lst -> fold_or approx lst
	| T.Exists (x, i, e) ->
	    let j = I.flip i in
	      upper prec (Env.extend x (T.Interval j) env) e
	| T.Forall (x, i, e) ->
	    let m = T.Dyadic (I.midpoint prec 1 i) in
	      upper prec (Env.extend x m env) e	
and
  uppera prec env e =
    let approx = uppera prec env in
      match e with
	| T.Var x -> approx (Env.get x env)
	| T.RealVar (_, i) -> I.flip i
	| T.Dyadic q -> I.of_dyadic q
	| T.Interval i -> i
	| T.Cut (_, i, _, _) -> I.flip i
	| T.Binary (op, e1, e2) ->
	    let i1 = approx e1 in
	    let i2 = approx e2 in
	      bin_apply ~prec ~round:D.up op i1 i2
	| T.Unary (op, e) ->
	    let i = approx e in
	      unary_apply ~prec ~round:D.up op i
	| T.Power (e, k) ->
	    let i = approx e in
	      I.pow ~prec ~round:D.up i k
	
end;;

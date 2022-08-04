(* 	Shey Pemberton	*)

type proposition =
  | False 
  | True 
  | Var of string 
  | And of proposition * proposition 
  | Or of proposition * proposition 
  | Not of proposition 
  | Imply of proposition * proposition
  | Equiv of proposition * proposition 
  | If of proposition * proposition * proposition ;;

(* ifify p - p is a propositional expression. 
Use rules 1-5, translate p to equivalent if-expression, and return it. *)
let ifify p = 
	let rec ify p = 
		match p with
		| Not a -> If(ify a, False, True)  
		| And(a,b) -> If(ify a, ify b, False) 
		| Or(a,b) -> If(ify a, True, ify b) 
		| Imply(a,b) -> If(ify a, ify b, True) 
		| Equiv(a,b) -> let b' = ify b in If(ify a, b', (If(b', False, True)))  
		| If(x,y,z) -> If((ify x), (ify y), (ify z)) 
		| _ -> p
	in ify p ;;
		

(* normalize c - c is an if-expression returned from ifify. 
translate c to equivalent normalized if-expression, and return it. *)			     			     			
let normalize c = 
	let rec norm c = 
		match c with
		
		| If(x,y',z') ->(match x with
				| If(x',y,z) -> norm(If(norm x', norm(If(y,y',z')), norm(If(z,y',z')))) 
				| a -> If(norm a, norm y', norm z')) 
		| _ -> c
	in norm c ;;



(* 	substitute c v b - helper function for simplify. c is normalized if-expression. v is variable name, and b is a Boolean value. 
	Return if-expression that is like c, but where each appearance of v is replaced by b. *)
let substitute c v b = 
	let rec subby c v b = 
		match c with
		| If(x,y,z) -> If(subby x v b, subby y v b, subby z v b) 
		| _ -> (if c=v then b
			else c) 
	in subby c v b ;; 


(* 	simplify c - c is normalized if-expression returned from normalize. 
	Use rules 7-11, simplify c and return resulting if-expression: true or false. *)
let rec simplify c = 
		match c with 
		| If(True,y,z) -> simplify y 
		| If(False,y,z) -> simplify z 
		| If(x,True,False) -> simplify x 
		| If(x,y,z) -> (if y=z then (simplify (If(x, (simplify (substitute y x True)), (simplify (substitute z x False)))))
				else simplify y )
		| _ -> c;;		

(* 	tautology p - p is propositional expression. Not rec. Return if p is tautology, false otherwise. *)
let tautology prop = 
	let p = simplify(normalize(ifify(prop))) in 
	if p=True then true
	else false;; 



(* TEST CASES *)
(* VARIABLES FOR TEST CASES *)
let p = Var "p";;
let q = Var "q";; 
let r = Var "r";;

(* TAUTOLOGIES - evaluate to "true" *)
let t1 = Imply((Not(And(p,q))),Or((Not p),(Not q)));; (* given in proj1.tml *)
let t2 = Imply(And(Or(p,q),Not q),Not q);;
let t3 = Or((Imply(p,q)),(Imply(q,p)));;
let t4 = Or(p, Not p);;
let t5 = Or(p, And(p,q));;
let contrapositive = Equiv(Imply(p,q),(Imply(Not p, Not q)));;
let deMorgan1 = Equiv(Not(Or(p,q)), And(Not p, Not q));;
let deMorgan2 = Equiv(Not(And(p,q)), Or(Not p, Not q));;

(* CONTRADICTIONS - evaluate to "false" *) 	
let contradiction1 = And(p, Not p);;
let contradiction2 = And(Or(p,q), Not p);;

(* CONTINGENCIES - evaluate to "false" *)
let contingency1 = Imply(Imply(p,q), And(p,q));;
let contingency2 = And(Imply(p,q),Equiv(Not p, q));;

(* TEST EACH FUNCTION - as shown in proj1.ml *)
let ifified = ifify t1;; 
let normalized = normalize(ifified);; 
substitute (If(p,(If(p, False, q)),p)) p True;;  (* should evaluate to If(True, If(True, False, Var "q"), True) *)
let simplified = simplify(normalized);;

(* EVALUATE TEST CASES *)
(* true *)
tautology t1;;
tautology t2;;
tautology t3;;
tautology t4;;
tautology t5;;
tautology contrapositive;;
tautology deMorgan1;;
tautology deMorgan2;;
(* false*)
tautology contradiction1;; 
tautology contradiction2;;
tautology contingency1;;
tautology contingency2;;




(* 
# #use "proj1.ml";;
type proposition =
    False
  | True
  | Var of string
  | And of proposition * proposition
  | Or of proposition * proposition
  | Not of proposition
  | Imply of proposition * proposition
  | Equiv of proposition * proposition
  | If of proposition * proposition * proposition
val ifify : proposition -> proposition = <fun>
val normalize : proposition -> proposition = <fun>
val substitute : proposition -> proposition -> proposition -> proposition =
  <fun>
val simplify : proposition -> proposition = <fun>
val tautology : proposition -> bool = <fun>
val p : proposition = Var "p"
val q : proposition = Var "q"
val r : proposition = Var "r"
val t1 : proposition =
  Imply (Not (And (Var "p", Var "q")), Or (Not (Var "p"), Not (Var "q")))
val t2 : proposition =
  Imply (And (Or (Var "p", Var "q"), Not (Var "q")), Not (Var "q"))
val t3 : proposition =
  Or (Imply (Var "p", Var "q"), Imply (Var "q", Var "p"))
val t4 : proposition = Or (Var "p", Not (Var "p"))
val t5 : proposition = Or (Var "p", And (Var "p", Var "q"))
val contrapositive : proposition =
  Equiv (Imply (Var "p", Var "q"), Imply (Not (Var "p"), Not (Var "q")))
val deMorgan1 : proposition =
  Equiv (Not (Or (Var "p", Var "q")), And (Not (Var "p"), Not (Var "q")))
val deMorgan2 : proposition =
  Equiv (Not (And (Var "p", Var "q")), Or (Not (Var "p"), Not (Var "q")))
val contradiction1 : proposition = And (Var "p", Not (Var "p"))
val contradiction2 : proposition = And (Or (Var "p", Var "q"), Not (Var "p"))
val contingency1 : proposition =
  Imply (Imply (Var "p", Var "q"), And (Var "p", Var "q"))
val contingency2 : proposition =
  And (Imply (Var "p", Var "q"), Equiv (Not (Var "p"), Var "q"))
val ifified : proposition =
  If (If (If (Var "p", Var "q", False), False, True),
   If (If (Var "p", False, True), True, If (Var "q", False, True)), True)
val normalized : proposition =
  If (Var "p",
   If (Var "q",
    If (False,
     If (Var "p", If (False, True, If (Var "q", False, True)),
      If (True, True, If (Var "q", False, True))),
     True),
    If (True,
     If (Var "p", If (False, True, If (Var "q", False, True)),
      If (True, True, If (Var "q", False, True))),
     True)),
   If (False,
    If (False,
     If (Var "p", If (False, True, If (Var "q", False, True)),
      If (True, True, If (Var "q", False, True))),
     True),
    If (True,
     If (Var "p", If (False, True, If (Var "q", False, True)),
      If (True, True, If (Var "q", False, True))),
     True)))
- : proposition = If (True, If (True, False, Var "q"), True)
val simplified : proposition = True
- : bool = true
- : bool = true
- : bool = true
- : bool = true
- : bool = true
- : bool = true
- : bool = true
- : bool = true
- : bool = false
- : bool = false
- : bool = false
- : bool = false
*)

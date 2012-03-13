(* --------------------------------------------	*)
(* denotational semantics definitions: in SML	*)
(*   = ds_imp.ml 				*)
(* --------------------------------------------	*)

(* --------------------------------------------	*)
(*   Skeleton for Lab;				*)
(*     fill in all missing sections.		*)
(* --------------------------------------------	*)

(* --------------------------------------------	*)
(* Imp: expressions language (Watt, Ex. 3.6)	*)
(*      with commands    (store).. 		*)
(*      and  definitions (evnironment).. 	*)
(*      --					*)
(*     (A nicer version of Ex. 4.7 from text)	*)
(* --------------------------------------------	*)

(* --------------------------------------------	*)
(* ---------- Abstract Syntax -----------------	*)

			(* terminal nodes of the syntax *)
type      Numeral  = int;

type      Ident    = string;

			(* parsed phrases of the abstract syntax *)
datatype
    Command =
              skip
            | assign   of Ident       * Expression
            | letin    of Declaration * Command
            | cmdcmd   of Command     * Command
            | ifthen   of Expression  * Command * Command
            | whiledo  of Expression  * Command
and
    Expression =
              num    of Numeral
    	    | False 
	    | True
    	    | id     of Ident
    	    | sumof  of Expression  * Expression
    	    | subof  of Expression  * Expression
    	    | prodof of Expression  * Expression
    	    | less   of Expression  * Expression
         (* | leten  of Declaration * Expression *)
    	    | notexp of Expression
and
    Declaration =
	      constdef of Ident * Expression
	    | vardef   of Ident * TypeDef
and
    TypeDef =
	      Bool | Int
	    ;


(* --------------------------------------------	*)
(* ---------- Semantic Domains ----------------	*)

type		Integer	= int;
type		Boolean	= bool;
type		Location= int;

datatype	Value	= integer     of int
			| truth_value of bool;

type		Storable  = Value;

datatype	Bindable  = value of Value | variable of Location;

datatype	Denotable = unbound | bound of Bindable ;

exception	fail;


(* --------------------------------------------	*)
(* ---------- Semantic Functions --------------	*)
(*  These declarations are automatically inferred
 *   from the defining equations below...

    type  Environ  =  Ident -> Denotable;
								    (..old..)
    type  Store    =  Location -> (Storable + undef + unused);

    type  execute   =  Command    -> Environ -> Store -> Store;
    type  evaluate  =  Expression -> Environ -> Store -> Value;
    type  elaborate =  Definition -> Environ -> Store -> (Environ * Store);

 *)


(* --------------------------------------------	*)
(* ---------- Auxiliary Semantic Functions ----	*)
fun sum   (x, y) = x + y:int;
fun diff  (x, y) = x - y:int;
fun prod  (x, y) = x * y:int;

fun lessthan  (x, y) = x < (y:int);

(* ---------- Storage   ---------- *)
(*
fun deallocate sto loc:Location = sto;	(* ... later *)
*)

datatype Sval  = stored of Storable | undef | unused;

	      (*          --bot---   --top---   ----data--------- *)
datatype Store = store of Location * Location * (Location -> Sval);

val sto_init  =  fn loc:Location => unused;
val sto_null  =  store( 1, 0, sto_init);

fun update (store(bot,top,data), loc, v) = 
	let fun new adr =  if adr=loc
			   then stored v else (data adr);
	in store( bot, top, new)
	end;
                                            
		(* fetch from store, and convert into Storable (=Value) *)
fun fetch  (store(bot,top,data), loc:Location)  =
	let fun stored_value(stored stble) = stble
	      | stored_value(unused)       = raise fail
	      | stored_value(undef)        = raise fail
	in stored_value( data loc)
	end;

		(* create a new "undefined" location in a store *)
fun allocate ( store(bot,top,data) )  =
	let val newtop = top+1
	    fun new adr =  if adr=newtop
			   then undef else (data adr);
	in (store( bot, newtop, new), newtop)
	end;


(* ---------- Envirionment   ---------- *)
type  Environ  =  Ident -> Denotable;

val env_null  =  fn i:Ident => unbound;
fun bind  (name, vl) =  fn idn => if idn=(name:Ident)
                                     then bound(vl) else unbound;
fun find  (env:Environ, idn)  =
	let fun getbv(bound bdbl) = bdbl
	      | getbv(unbound)    = raise fail
	in getbv( env idn)
	end;
fun overlay  (env', env:Environ)  =
	fn idn => let val val' = env' idn
	          in if val'<>unbound then val'
	                              else env idn
		  end;

(* ---------- Etc....	   ----------	*)
(*    coerce a Bindable into a Value..	*)
fun coerc (sto, value v)      = v
  | coerc (sto, variable loc) = fetch(sto,loc);


(* ---------- Initialize system  ---------- *)


(* --------------------------------------------	*)
(* ---------- Semantic Equations --------------	*)

				(* from integer to Value *)
fun  valuation ( n )   = integer(n)
and
     execute ( skip  ) env sto  = sto
  |  execute ( assign(name,exp) ) env sto  =
     		let val rhs = evaluate exp env sto
     		    val variable loc = find( env,name)
		in  update( sto, loc, rhs)
		end
  |  execute ( letin(def,c) ) env sto =
     		...
  |  execute ( cmdcmd(c1,c2) ) env sto  =
		...
  |  execute ( ifthen(e,c1,c2) ) env sto =
     		...
  |  execute ( whiledo(e,c) ) en st =
     		...
and
     			(* simple, just build a Value *)
     evaluate ( num(n) )  env sto  = integer n
  |  evaluate ( True   )  env sto  = truth_value true
  |  evaluate ( False  )  env sto  = truth_value false

     			(* lookup id, and  coerce as needed *)
  |  evaluate ( id(n)  )  env sto  = coerc( sto, find(env,n) )

     			(* get values, and compute result *)
  |  evaluate ( sumof (e1,e2) ) env sto = 
     		let val integer(i1) = evaluate e1 env sto
     		    val integer(i2) = evaluate e2 env sto
		in  integer( sum(i1,i2) )
		end
  |  evaluate ( subof (e1,e2) ) env sto =
		...
  |  evaluate ( prodof(e1,e2) ) env sto =
		...
  |  evaluate ( less(e1,e2) ) env sto =
		...
  |  evaluate ( notexp(e) ) env sto =
		...

  (* ------- * Later...
     			(* layer enviroinment, and compute result *)
  |  evaluate ( leten(def,e) ) env sto =
     		let val (env', sto') = elaborate def env sto
		in  evaluate e (overlay (env', env)) sto'
		end
   * ------- *)
and
     elaborate ( constdef(name,e) ) env sto =
     		let val v = evaluate e env sto
		in  ( bind(name, value v), sto )
		end
  |  elaborate ( vardef(name,tdef) ) env sto =
		...
  ;


(* ============================================	*)
(* ---------- Test it..! ----------------------	*)

val e1 = num(2);
val e2 = sumof(num(1),num(2));
evaluate e1 env_null sto_null;		(*  = 2 *)
evaluate e2 env_null sto_null;		(*  = 3 *)

evaluate (sumof(num(1), prodof(num(2),num(3)))) env_null sto_null; (*  = 7 *)

val dx = constdef("x",num(2));	(* a declaration *)
elaborate dx env_null sto_null;

(*
evaluate (  letin( dx, sumof( num(1), id("x") ))  ) env_null sto_null; (* = 3 *)
 *)

(* ----------------------------------------------- *)
(*   let const x ~ 2
 *   in let var y : int
 *      in  y:= 3
 *          if x<y then y:=1
 *                 else y:=2
 *)
val pgm = 
  letin( constdef( "x", num(2)),
         letin( vardef( "y", Int),
		cmdcmd( assign( "y", num(3)),
		        ifthen( less(id("x"),id("y")),
			        assign("y",num(1)),
			        assign("y",num(2))
				)
			)
		)
         )
  ;
execute pgm  env_null sto_null;
				(* dump the store.... *)
                (* y *)
map ($ fetch it) [ 1 ];

(* ----------------------------------------------- *)
(*   let const x ~ 2
 *   in let var     y : int
 *      in y := 3;
 *         let var z : int
 *         in  z:= 0
 *             z := z+1
 *)
val x = id("x");	(* a shorthand... *)
val y = id("y");
val z = id("z");
val pgm3 = 
  ...

(*  form, and run program.3  *)

				(* dump the store.... *)
(*                (* y  z *)
map ($ fetch sto3) [ 1, 2 ];
 *)
				(* dump the store.... *)
fun dump (sto as store(lo, hi, data) ) =
    map ($ fetch sto) (from lo hi);
dump sto3;


(* ----------------------------------------------- *)
(*   let const x ~ 2
 *   in let var     y : int
 *      in y := 3;
 *         let var z : int
 *         in  z:= 0		{ multiply z = x*y }
 *             while 0<y do  z := z+x; y := y-1
 *)

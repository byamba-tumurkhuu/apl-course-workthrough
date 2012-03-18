-----------------------------------------------------------------------------
--
-- Module      ::  DSemImp
-- APL Lab Template in Haskell!!
--
-- ----------------------------------------------	--
-- denotational semantics definitions: in Haskell	--
-- ----------------------------------------------	--
-- Imp: expressions language (Watt, Ex. 3.6)	--
--      with commands    (store).. 		--
--      and  definitions (environment).. 	--
--
--     (A nicer version of Ex. 4.7 from text)	--
-- --------------------------------------------	--
--
-----------------------------------------------------------------------------
module DSemImp where

import Debug.Trace
import Test.HUnit 
import Char

-- --------------------------------------------	--
-- ---------- Abstract Syntax -----------------	--

			-- terminal nodes of the syntax --

type Numeral = Int
type Ident = String

data Command = Skip
               | Assign   (Ident,       Expression)
               | Letin    (Declaration, Command   )
               | Cmdcmd   (Command,     Command   )
               | Ifthen   (Expression,  Command, Command)
               | Whiledo  (Expression,  Command   )

data Expression = Num Numeral
                  | False_
                  | True_
                  | Notexp   Expression
                  | Id       Ident
                  | Sumof   (Expression,  Expression)
                  | Subof   (Expression,  Expression)
                  | Prodof  (Expression,  Expression)
                  | Less    (Expression,  Expression)
                  | Leten   (Declaration, Expression)
                  deriving Show

data Declaration = Constdef (Ident,  Expression) | Vardef   (Ident,  TypeDef) 
                   deriving Show

data TypeDef = Bool | Int deriving Show

-- --------------------------------------------	--
-- ---------- Semantic Domains ----------------	--

type Integer = Int
type Boolean = Bool
type Location = Int

data Value = IntValue Int | TruthValue  Bool
             deriving (Eq, Show)

type Storable = Value

data Bindable = Const Value | Variable Location
                deriving (Eq, Show)

data Denotable = Unbound | Bound Bindable
                 deriving (Eq, Show)

-- --------------------------------------------	--
-- ---------- Semantic Functions --------------	--
valuation :: Int         -> Value
evaluate  :: Expression  -> Environ -> Store ->  Value
elaborate :: Declaration -> Environ -> Store ->  (Environ, Store)
execute   :: Command     -> Environ -> Store ->  Store

-- --------------------------------------------	--
-- ---------- Auxiliary Semantic Functions ----	--
add       (x, y) = x + y
diff      (x, y) = x - y
prod      (x, y) = x * y
lessthan  (x, y) = x < y

-- ---------- Storage   ---------- --
-- fun deallocate sto loc:Location = sto	-- ... later --

data Sval  = Stored Storable | Undef | Unused 
             deriving (Eq, Show)

-- The actual storage in a Store
type DataStore = Location -> Sval

--	                 --bot---   --top---  --data---
data Store = Store (Location,  Location,  DataStore)

update :: (Store, Location, Value) -> Store
update (Store(bot, top, sto), loc, v) =
	let new adr = if adr == loc then Stored v else (sto adr)
	in Store(bot, top, new)

		-- fetch from store, and convert into Storable (=Const)
fetch :: (Store, Location) -> Storable
fetch  (Store(bot, top, sto), loc)  =
	let stored_value(Stored stble) = stble
	    stored_value(Unused)       = error ("Store: Unused")
	    stored_value(Undef)        = error ("Store: Undefined ")
	in  stored_value(sto loc)

		-- create a new "undefined" location in a store
allocate :: Store -> (Store, Location)
allocate ( Store(bot, top, sto) )  =
	let newtop  = top + 1
	    new adr = if adr == newtop then Undef else (sto adr)
	in (Store( bot, newtop, new), newtop)

-- ---------- Envirionment   ----------
type  Environ  =  Ident -> Denotable

bind :: (Ident, Bindable) -> Environ
bind  (name, val) =  \id -> if id == name then Bound(val) else Unbound

-- look through the layered environment bindings
find :: (Environ, Ident) -> Bindable
find  (env, id)  =
  let getbv(Bound bdbl) = bdbl
      getbv(Unbound)    = error ("undefined: " ++ id)
  in getbv( env id)

overlay :: (Environ, Environ) -> Environ
overlay  (env', env)  =
	\id -> let val = env' id
	       in  if val /= Unbound then val else env id

-- ---------- Etc...
--    coerce a Bindable into a Const..
coerc :: (Store, Bindable) -> Value
coerc (sto, Const v)      = v
coerc (sto, Variable loc) = fetch(sto,loc)

-- ---------- Initialize system  ----------
env_null :: Environ
env_null =  \i -> Unbound

--  store_null =  empty (=0), addressing starts at 1
sto_init :: DataStore
sto_init =  \loc -> Unused

sto_null :: Store
sto_null =  Store( 1, 0, sto_init)

-- --------------------------------------------
-- ---------- Semantic Equations --------------

				-- from integer to Const Value
valuation ( n ) = IntValue(n)

execute ( Skip ) env sto = sto

execute ( Assign(name, exp) ) env sto  =
     		let rhs = evaluate exp env sto
     		    Variable loc = find(env, name)
     		in  update( sto, loc, rhs)

execute ( Letin(dec, c) ) env sto =
  let (env', sto') = elaborate(dec) env sto
  in  execute (c) (overlay(env', env)) sto'

execute ( Cmdcmd(c1, c2) ) env sto  =
  let sto' = (execute(c1) env sto)
  in  execute c2 env sto'

execute ( Ifthen(e, c1, c2) ) env sto =
  if (evaluate(e) env sto) == TruthValue True 
  then execute(c1) env sto
  else execute(c2) env sto
                  
execute ( Whiledo(e, c) ) env sto =
  let dowhile env sto = if evaluate(e) env sto == TruthValue True 
                        then dowhile env (execute(c) env sto)
                        else sto
  in  dowhile env sto


     			-- simple, just build a Const
evaluate ( Num(n)  )  env sto  = IntValue n
evaluate ( True_   )  env sto  = TruthValue  True
evaluate ( False_  )  env sto  = TruthValue  False

     			-- lookup id, and  coerce as needed
evaluate ( Id(n)  )  env sto  = coerc(sto, find(env, n) )

     			-- get Consts, and compute result
evaluate ( Sumof(e1,e2) ) env sto =
  let IntValue i1 = evaluate e1 env sto
      IntValue i2 = evaluate e2 env sto
  in  IntValue  ( add(i1,i2) )

evaluate ( Subof(e1,e2) ) env sto =
  let IntValue i1 = evaluate e1 env sto
      IntValue i2 = evaluate e2 env sto
  in IntValue (diff(i1, i2))

evaluate ( Prodof(e1,e2) ) env sto =
  let IntValue i1 = evaluate e1 env sto
      IntValue i2 = evaluate e2 env sto
  in  IntValue (prod(i1, i2))

evaluate ( Less(e1, e2) ) env sto =
  let IntValue i1 = evaluate e1 env sto
      IntValue i2 = evaluate e2 env sto
  in  TruthValue (lessthan(i1, i2))

evaluate ( Notexp(e) ) env sto = 
  let i = evaluate e env sto
      ev :: Value -> Bool
      ev (TruthValue x) = not x
      ev (IntValue x) = error "Invalid operation"
  in  TruthValue (ev i)

evaluate ( Leten(def, e) ) env sto =
  let (env', sto') = elaborate def env sto
  in  evaluate e (overlay (env', env)) sto'

elaborate ( Constdef(name, e) ) env sto =
  let v = evaluate e env sto
  in  ( bind(name, Const  v), sto )

elaborate ( Vardef(name, tdef) ) env sto =
  let (sto', loc) = allocate sto
  in  ( bind(name, Variable loc), sto' )


----------------------------------------------------------------------
---------------------------         ----------------------------------
--------------------------- TESTING ----------------------------------
---------------------------         ----------------------------------
----------------------------------------------------------------------

dump sto@(Store (lo, hi, d)) = map (\l -> trace (show l) (fetch(sto, l))) [lo..hi]

e1 = Num(2)
e2 = Sumof(Num(1), Num(2))
dx = Constdef("x", Num(2))	-- a declaration

-------------------------------------------------
--                pgm1
--   let const x ~ 2
--   in let var y : int
--      in  y:= 3
--          if x<y then y:=1
--                 else y:=2
pgm1 = Letin( Constdef( "x", Num(2)),
             Letin( Vardef( "y", Int),
                    Cmdcmd( Assign( "y", Num(3)),
                            Ifthen( Less(Id("x"), Id("y")), Assign("y", Num(1)), Assign("y", Num(2)))
                          )
                  )
           )
store1 = execute pgm1 env_null sto_null

-------------------------------------------------
--                pgm2
x = Id("x")
y = Id("y")
z = Id("z")
pgm2 = Letin( Constdef( "x", Num(2)),
                        Letin( Vardef(  "y", Int),
                               Cmdcmd( Assign( "y", Num(3)),
                                       Letin ( Vardef( "z", Int),
                                               Cmdcmd( Assign("z", Num(0)), Assign("z", Sumof(z, Num(1))))
                                             )
                                    )
                             )
            )
store2 = execute pgm2 env_null sto_null
-------------------------------------------------

-------------------------------------------------
--                pgm3
pgm3 = Letin(Constdef("x", Num(2)),
             Letin( Vardef("y", Int),
                    Cmdcmd(Assign("y", Num(3)),
                           Letin(Vardef("z", Int),
                                 Cmdcmd(Assign("z", Num(0)),
                                        Whiledo(Less(Num(0), y),
                                                Cmdcmd(Assign("z", Sumof(z, x)),
                                                       Assign("y",Subof(y, Num(1)))
                                                      )
                                               )
                                       )
                                 )
                          )
                  )
            )
store3 = execute pgm3 env_null sto_null
-------------------------------------------------
                                    
impTests = TestList [ "test evaluate1" ~: (evaluate e1 env_null sto_null) ~=? (IntValue 2) ,
                      "test evaluate2" ~: (evaluate e2 env_null sto_null) ~=? (IntValue 3) ,
                      "test evaluate3" ~: (evaluate (Sumof(Num(1), Prodof(Num(2), Num(3)))) env_null sto_null) ~=? (IntValue 7),
                      "test Leten1" ~: (evaluate (Leten(dx, Sumof(Num(1), Id("x")))) env_null sto_null) ~=? (IntValue 3),
                      "test store1" ~: (fetch(store1, 1)) ~=? (IntValue 1), 
                      "test store2" ~: (fetch(store2, 1)) ~=? (IntValue 3),
                      "test store2" ~: (fetch(store2, 2)) ~=? (IntValue 1),
                      "test store3" ~: (fetch(store3, 1)) ~=? (IntValue 0),
                      "test store3" ~: (fetch(store3, 2)) ~=? (IntValue 6)
                    ]

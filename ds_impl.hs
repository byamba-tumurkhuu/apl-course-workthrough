-----------------------------------------------------------------------------
--
-- Module      ::  DSem_imp
-- APL Lab Template in Haskell!!
--
-- ----------------------------------------------	--
-- denotational semantics definitions: in Haskell	--
-- ----------------------------------------------	--
-- Imp: expressions language (Watt, Ex. 3.6)	--
--      with commands    (store).. 		--
--      and  definitions (evnironment).. 	--
--
--     (A nicer version of Ex. 4.7 from text)	--
-- --------------------------------------------	--
--
-----------------------------------------------------------------------------
module DSemImp (
-- impTests        -- export the test results...
) where

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
elaborate :: Declaration -> Environ -> Store ->  (Environ,Store)
execute   :: Command     -> Environ -> Store ->  Store

-- --------------------------------------------	--
-- ---------- Auxiliary Semantic Functions ----	--
add   (x, y) = x + y
diff  (x, y) = x - y
prod  (x, y) = x * y

lessthan  (x, y) = x < y

-- ---------- Storage   ---------- --
-- fun deallocate sto loc:Location = sto	-- ... later --

data Sval  = Stored Storable | Undef | Unused

-- The actual storage in a Store
type DataStore = Location -> Sval

--	                 --bot---   --top---  --data---
data Store = Store (Location,  Location,  DataStore)

update :: (Store, Location, Value) -> Store
update (Store(bot,top,sto), loc, v) =
	let new adr = if adr==loc
			      then Stored v else (sto adr)
	in Store( bot, top, new)

		-- fetch from store, and convert into Storable (=Const)
fetch ::(Store,Location) -> Storable
fetch  (Store(bot,top,sto), loc)  =
	let stored_value(Stored stble) = stble
	    stored_value(Unused)       = error ("Store: Unused")
	    stored_value(Undef)        = error ("Store: Undefined ")
	in  stored_value(sto loc)

		-- create a new "undefined" location in a store
allocate :: Store -> (Store, Location)
allocate ( Store(bot,top,sto) )  =
	let newtop  = top+1
	    new adr = if adr==newtop
			      then Undef else (sto adr)
	in (Store( bot, newtop, new), newtop)

-- ---------- Envirionment   ----------
type  Environ  =  Ident -> Denotable

bind :: (Ident,Bindable) -> Environ
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
	       in  if val/=Unbound then val else env id

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

execute ( Assign(name,exp) ) env sto  =
     		let rhs = evaluate exp env sto
     		    Variable loc = find( env,name)
     		in  update( sto, loc, rhs)

execute ( Letin(def, c) ) env sto =
  let (env', sto') = elaborate(def) env sto
  in 
    execute (c) (overlay(env',env)) sto'

execute ( Cmdcmd(c1, c2) ) env sto  =
  let sto' = (execute(c1) env sto)
  in 
    execute c2 env sto'

execute ( Ifthen(e, c1, c2) ) env sto =
  if (evaluate(e) env sto) == TruthValue True 
  then execute(c1) env_null sto
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
evaluate ( Id(n)  )  env sto  = coerc( sto, find(env,n) )

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

evaluate ( Less(e1,e2) ) env sto =
  let IntValue i1 = evaluate e1 env sto
      IntValue i2 = evaluate e2 env sto
  in  TruthValue (lessthan(i1, i2))

evaluate ( Notexp(e) ) env sto = 
  let i = evaluate e env sto
      ev :: Value -> Bool
      ev (TruthValue x) = not x
      ev (IntValue x) = error "Invalid operation"
  in  TruthValue (ev i)

{-- ------- * Later...
     			-- layer environment, and compute result
evaluate ( leten(def,e) ) env sto =
  let (env', sto') = elaborate def env sto
  in  evaluate e (overlay (env', env)) sto'
   ------- -
-}

elaborate ( Constdef(name, e) ) env sto =
  let v = evaluate e env sto
  in  ( bind(name, Const  v), sto )

elaborate ( Vardef(name,tdef) ) env sto =
  let (sto',loc) = allocate sto
  in  ( bind(name, Variable loc), sto' )

-- ============================================	 --

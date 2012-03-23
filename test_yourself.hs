module DSemImp where

import Debug.Trace
import Test.HUnit 
import Char
import Text.Show.Functions

-- --------------------------------------------	--
-- ---------- Abstract Syntax -----------------	--
type Numeral = Int
type Ident = String

data Command = Skip
               deriving Show

data Expression =

data Declaration =  

data TypeDef = Integer | Boolean deriving show 

-- --------------------------------------------	--
-- ---------- Semantic Domains ----------------	--

type Integer = Int
type Boolean = Bool
type Location = Int

data Value = IntValue Integer | TruthValue Boolean deriving show

type Storable = Value
type Argument = Value

type FunctionType   =
type ProcedureType  =

data Bindable = 

instance Eq Bindable where
  (Procedure p1) == (Procedure p2) = False
  (Function p1) == (Function p2) = False
  (Const v1) == (Const v2) = v1 == v2
  (Variable l1) == (Variable l2) = l1 == l2

data FormalParameter = 
data ActualParameter = 

-- --------------------------------------------	--
-- ---------- Semantic Functions --------------	--
valuation     ::
evaluate      ::
elaborate     ::
execute       ::
bindParameter ::
giveArgument  :: 

bindParameter 
giveArgument

-- --------------------------------------------	--
-- ---------- Auxiliary Semantic Functions ----	--
add       (x, y) = x + y
diff      (x, y) = x - y
prod      (x, y) = x * y
lessthan  (x, y) = x < y

-- ---------- Storage   ---------- --
-- fun deallocate sto loc:Location = sto	-- ... later --

data Sval = Stored Storable | Undefined | Unused deriving (Eq, Show)

-- The actual storage in a Store
type DataStore = Location -> Sval

--bot---   --top---  --data---
data Store = Store (Location,  Location,  DataStore)

update :: (Store, Location, Value) -> Store
update (Store(bot, top, sto), loc, v) =

-- coerce a Bindable into a Const..
coerc :: (Store, Bindable) -> Value
coerc (sto, Const v)      = v
coerc (sto, Variable loc) = fetch(sto,loc)

-- fetch from store, and convert into Storable (=Const)
fetch :: (Store, Location) -> Storable
fetch  (Store(bot, top, sto), loc)  =
  let f Stored s = s
      f Unused   = error "Unused location" ++ show loc
      f Undefined = error "Undefined location" ++ show loc
  f (sto loc)

-- create a new "undefined" location in a store
allocate :: Store -> (Store, Location)
allocate ( Store(bot, top, sto) )  = 
  let newTop = top + 1
      new adr = if (newTop == adr) Undefined else  sto adr
  in (Store(bot, newTop, new), newTop)

-- ---------- Envirionment   ----------
data Denotable = Bound Value | Unbound
type  Environ  = Ident -> Value

bind :: (Ident, Bindable) -> Environ
bind (name, val) = \i -> if (i == name) Bound val else Unbound


-- look through the layered environment bindings
find :: (Environ, Ident) -> Bindable
find  (env, id)  =
  let getbv Bound b = b
      getbv _       = error "Undefined: " ++ id
  in  getbv (env id)

overlay :: (Environ, Environ) -> Environ
overlay  (env', env)  = \i -> if (evn' i != Unbound) env' i else env i

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
  let val = evaluate exp env sto
  in  update(sto, loc, val)

execute ( Letin(dec, c) ) env sto =

execute ( Cmdcmd(c1, c2) ) env sto  =

execute ( Ifthen(e, c1, c2) ) env sto =
                  
execute ( Whiledo(e, c) ) env sto =

execute (Procall(procName, param)) env sto = 

     			-- simple, just build a Const
evaluate ( Num(n)  )  env sto  = IntValue n
evaluate ( True_   )  env sto  = TruthValue  True
evaluate ( False_  )  env sto  = TruthValue  False

     			-- lookup id, and  coerce as needed
evaluate ( Id(n)  )  env sto  = 

     			-- get Consts, and compute result
evaluate ( Sumof(e1,e2) ) env sto =

evaluate ( Subof(e1,e2) ) env sto =

evaluate ( Prodof(e1,e2) ) env sto =

evaluate ( Less(e1, e2) ) env sto =

evaluate ( Notexp(e) ) env sto = 

evaluate ( Leten(def, e) ) env sto =

evaluate (Funcall(funcName, param)) env sto =  

elaborate ( Constdef(name, e) ) env sto =

elaborate ( Vardef(name, tdef) ) env sto =

elaborate (Funcdef(name, fp, e)) env sto =

elaborate (Procdef(procName, fp, c)) env sto =

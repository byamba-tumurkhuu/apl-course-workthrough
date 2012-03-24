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
               | Assign  (Ident, Expression)
               | Letin   (Declaration, Command)
               | Cmdcmd  (Command, Command)
               | Ifthen  (Expression, Command, Command)
               | Whiledo (Expression, Command)
               | Procall (Ident, ActualParameter)
               deriving Show

data Expression = Num Numeral 
                  | Notexp Expression
                  | Id Ident
                  | Sumof   (Expression,  Expression)
                  | Subof   (Expression,  Expression)
                  | Prodof  (Expression,  Expression)
                  | Less    (Expression,  Expression)
                  | Leten   (Declaration, Expression)
                  | Funcall (Ident,       ActualParameter)
                  deriving Show

data Declaration = Funcdef (Ident, FormalParameter, Expression)
                   |  Procdef(Ident, FormalParameter, Command)
                   | Vardef(Ident, TypeDef)
                   | Constdef(Ident, Expression)
                   deriving Show

data TypeDef = Integer | Boolean deriving Show 

-- --------------------------------------------	--
-- ---------- Semantic Domains ----------------	--

type Integer = Int
type Boolean = Bool
type Location = Int

data Value = IntValue Int | TruthValue Boolean deriving (Eq, Show)

type Storable = Value
type Argument = Value
data Sval = Stored Storable | Undefined | Unused deriving (Eq, Show)


-- ---------- Storage   ---------- --
-- The actual storage in a Store
type DataStore = Location -> Sval
--bot---   --top---  --data---
data Store = Store (Location,  Location,  DataStore)

type FunctionType   = Argument -> Store -> Value
type ProcedureType  = Argument -> Store -> Store

data Bindable = Function FunctionType | Procedure ProcedureType | Const Value | Variable Location 
                deriving Show

instance Eq Bindable where
  (Procedure p1) == (Procedure p2) = False
  (Function p1) == (Function p2) = False
  (Const v1) == (Const v2) = v1 == v2
  (Variable l1) == (Variable l2) = l1 == l2

data FormalParameter = FormalParameter (Ident, TypeDef) deriving Show
data ActualParameter = ActualParameter Expression deriving Show

-- --------------------------------------------	--
-- ---------- Semantic Functions --------------	--
valuation     :: Int -> Value 
evaluate      :: Expression  -> Environ -> Store -> Value
elaborate     :: Declaration -> Environ -> Store -> (Environ, Store)
execute       :: Command     -> Environ -> Store  -> Store
bindParameter :: FormalParameter -> Argument -> Environ
giveArgument  :: ActualParameter -> Environ  -> Store   -> Value

bindParameter (FormalParameter(name, tdef)) = \arg -> bind(name, Const arg)
giveArgument  (ActualParameter e) env sto = evaluate e env sto

-- --------------------------------------------	--
-- ---------- Auxiliary Semantic Functions ----	--
add       (x, y) = x + y
diff      (x, y) = x - y
prod      (x, y) = x * y
lessthan  (x, y) = x < y


update :: (Store, Location, Value) -> Store
update (Store(bot, top, sto), loc, v) =
  let f = \l -> if l == loc then Stored v else sto l
  in Store(bot, top, f)

-- coerce a Bindable into a Const..
coerc :: (Store, Bindable) -> Value
coerc (sto, Const v)      = v
coerc (sto, Variable loc) = fetch(sto,loc)

-- fetch from store, and convert into Storable (=Const)
fetch :: (Store, Location) -> Storable
fetch  (Store(bot, top, sto), loc)  =
  let f (Stored s) = s
      f Unused   = error ("Unused location" ++ show loc)
      f Undefined = error ("Undefined location" ++ show loc)
  in  f (sto loc)

-- create a new "undefined" location in a store
allocate :: Store -> (Store, Location)
allocate ( Store(bot, top, sto) )  = 
  let newTop = top + 1
      new adr = if (newTop == adr) then Undefined else  sto adr
  in (Store(bot, newTop, new), newTop)

-- ---------- Envirionment   ----------
data Denotable = Bound Value | Unbound deriving Eq
type  Environ  = Ident -> Denotable

bind :: (Ident, Bindable) -> Environ
bind (name, val) = \i -> if (i == name) then Bound val else Unbound


-- look through the layered environment bindings
find :: (Environ, Ident) -> Bindable
find  (env, id)  =
  let getbv (Bound b) = b
      getbv _         = error ("Undefined: " ++ id)
  in  getbv (env id)

overlay :: (Environ, Environ) -> Environ
overlay  (env', env)  = \i -> if (env' i /= Unbound) then env' i else env i

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
      Variable loc = find(env, name)
  in  update(sto, loc, val)

execute ( Letin(dec, c) ) env sto =
  let (env', sto') = elaborate dec env sto
  in  execute c (overlay(env', env)) sto'

execute ( Cmdcmd(c1, c2) ) env sto  =
  let sto' = execute c1 env sto
  in execute c2 env sto'

execute ( Ifthen(e, c1, c2) ) env sto =
  if evaluate e env sto == TruthValue True
  then execute c1 env sto
  else execute c2 env sto
                  
execute ( Whiledo(e, c) ) env sto =
  let doWhile sto =  if evaluate e env sto  == TruthValue True
                     then doWhile (execute c env sto)
                     else sto
  in doWhile sto

execute (Procall(procName, param)) env sto = 
  let Procedure proc = find(env, procName)
      arg = giveArgument param env sto
  in proc arg sto


     			-- simple, just build a Const
evaluate ( Num(n)  )  env sto  = IntValue n

     			-- lookup id, and  coerce as needed
evaluate ( Id n )  env sto  =  coerc(sto, find(env, n))

     			-- get Consts, and compute result
evaluate ( Sumof(e1,e2) ) env sto =
  let IntValue i1 = evaluate e1 env sto
      IntValue i2 = evaluate e2 env sto
  in IntValue (add(i1, i2))

evaluate ( Subof(e1,e2) ) env sto =
  let IntValue i1 = evaluate e1 env sto
      IntValue i2 = evaluate e2 env sto
  in IntValue (diff(i1, i2))

evaluate ( Prodof(e1,e2) ) env sto =
  let IntValue i1 = evaluate e1 env sto
      IntValue i2 = evaluate e2 env sto
  in IntValue (prod(i1, i2))

evaluate ( Less(e1, e2) ) env sto =
  let IntValue i1 = evaluate e1 env sto
      IntValue i2 = evaluate e2 env sto
  in TruthValue  (lessthan(i1, i2))

evaluate ( Notexp(e) ) env sto = 
  let TruthValue i = evaluate e env sto
  in  TruthValue (not i)

evaluate ( Leten(def, e) ) env sto =
  let (env', sto') = elaborate def env sto
  in  evaluate e (overlay(env', env)) sto'

evaluate (Funcall(funcName, param)) env sto =  
  let Function func = find(env, funcName)
      arg = giveArgument param env sto
  in  func arg sto

elaborate ( Constdef(name, e) ) env sto =
  let i = evaluate e env sto
  in (bind(name, Const i), sto)

elaborate ( Vardef(name, tdef) ) env sto =
  let (sto', loc) = allocate sto
  in  (bind(name, Variable loc), sto')

elaborate (Funcdef(name, fp, e)) env sto =
  let func arg = evaluate e (overlay(env', env))
                 where env' = bindParameter fp arg
  in  (bind(name, Function func), sto)

elaborate (Procdef(procName, fp, c)) env sto =
  let proc arg = execute c (overlay(env', env))
                 where env' = bindParameter fp arg
  in  (bind(procName, Procedure proc), sto)
  



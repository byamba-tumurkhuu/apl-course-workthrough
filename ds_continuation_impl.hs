-----------------------------------------------------------------------------
--
-- Byambatsogt Tumurkhuu
-- 982768
--
-- Module      ::  DSemImp
-- Denotation Semantics Continuation
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
import Text.Show.Functions

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
               | Procall  (Ident,       ActualParameter)
               deriving Show

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
                  | Funcall (Ident,       Expression)
                  deriving Show

data Declaration = Constdef  (Ident,  Expression) 
                   | Vardef  (Ident,  TypeDef) 
                   | Funcdef (Ident,  FormalParameter, Expression)
                   | Procdef (Ident,  FormalParameter, Command)
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
type Argument = Value

type FunctionType   = Argument -> Store -> Value
type ProcedureType  = Argument -> Store -> Store

data Bindable = Const Value | Variable Location | Procedure ProcedureType | Function FunctionType
                deriving (Show) -- deriving (Eq, Show)

instance Eq Bindable where
  (Procedure p1) == (Procedure p2) = False
  (Function p1) == (Function p2) = False
  (Const v1) == (Const v2) = v1 == v2
  (Variable l1) == (Variable l2) = l1 == l2

data Denotable = Unbound | Bound Bindable
                 deriving (Eq, Show)

data FormalParameter = FormalParameter (Ident, TypeDef) deriving Show
data ActualParameter = ActualParameter Expression deriving Show

-- Continuations
type CommandCont     = Store     -> Value
type ExpressionCont  = Storable  -> Value
type DeclarationCont = Environ   -> Store -> Value
type ProcedureCont   = Command   -> Store -> Value

-- --------------------------------------------	--
-- ---------- Semantic Functions --------------	--
valuation     :: Int         -> Value
evaluate      :: Expression  -> Environ -> ExpressionCont  -> Store -> Value
elaborate     :: Declaration -> Environ -> DeclarationCont -> Store -> Value
execute       :: Command     -> Environ -> CommandCont     -> Store -> Value

bindParameter :: FormalParameter -> Argument -> Environ
giveArgument  :: ActualParameter -> Environ  -> ExpressionCont -> Store -> Argument

bindParameter (FormalParameter(ident, typeDef)) = \arg -> bind(ident, (Const arg))
giveArgument  (ActualParameter(e)) env econt sto =  evaluate(e) env econt sto
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
  in  getbv( env id)

overlay :: (Environ, Environ) -> Environ
overlay  (env', env)  =
	\id -> let val = env' id
	       in  if val /= Unbound then val else env id

-- --------------------------------------------
-- ---------- Semantic Equations --------------

valuation ( n ) = IntValue(n)

evaluate ( Num(n) ) env econt sto = econt (IntValue n)
evaluate ( True_  ) env econt sto = econt (TruthValue True)
evaluate ( False_ ) env econt sto = econt (TruthValue False)

evaluate (Id(i)) env econt sto = 
  let d = find (env, i)
      f (Const v) = econt(v)
      f (Variable l) = econt (fetch (sto, l))
  in  f d

evaluate (Notexp exp) env econt sto = 
  let econt' = \(TruthValue t) -> econt(TruthValue (not t))
  in  evaluate exp env econt' sto

evaluate (Sumof(e1, e2)) env econt sto =
  let econt' = \(IntValue i1) -> evaluate e2 env (cont'' i1) sto
              where cont'' i1 = \(IntValue i2) -> econt(IntValue (add(i1, i2)))
  in  evaluate e1 env econt' sto

evaluate (Subof(e1, e2)) env econt sto =
  let econt' = \(IntValue i1) -> evaluate e2 env (cont'' i1) sto
              where cont'' i1 = \(IntValue i2) -> econt(IntValue (diff(i1, i2)))
  in  evaluate e1 env econt' sto

evaluate (Prodof(e1, e2)) env econt sto =
  let econt' = \(IntValue i1) -> evaluate e2 env (cont'' i1) sto
              where cont'' i1 = \(IntValue i2) -> econt(IntValue (prod(i1, i2)))
  in  evaluate e1 env econt' sto

evaluate (Less(e1, e2)) env econt sto =
  let econt' = \(IntValue i1) -> evaluate e2 env (cont'' i1) sto
              where cont'' i1 = \(IntValue i2) -> econt(TruthValue (lessthan(i1, i2)))
  in  evaluate e1 env econt' sto

-- evaluate (Funcall(ident, exp)) env econt sto =
--   let arg = giveArgument exp env sto
--       Function func = find(env, func)
--   in func arg sto

execute ( Skip ) env ccont sto = ccont sto

execute (Assign(name, exp) ) env ccont sto = 
  let Variable loc = find(env, name)
      econt = \storable -> ccont (update(sto, loc, storable))
  in  evaluate exp env econt sto

execute (Cmdcmd(c1, c2)) env ccont sto =
  let ccont' = \sto' -> execute c2 env ccont sto'
  in  execute c1 env ccont' sto

execute (Ifthen(e, c1, c2)) env ccont sto = 
  let econt = \b -> if b == TruthValue True
                    then execute c1 env ccont sto
                    else execute c2 env ccont sto
  in evaluate e env econt sto

execute ( Letin(dec, c) ) env ccont sto =
  let dcont = \env' -> \sto' -> execute c (overlay(env', env)) ccont sto'
  in  elaborate dec env dcont sto

elaborate ( Constdef(name, exp) ) env dcont sto =
  let econt = \v -> dcont (bind(name, Const v)) sto
  in  evaluate exp env econt sto

elaborate (Vardef(name, tdef) ) env dcont sto = 
  let (sto', loc) = allocate sto 
      env' = bind(name, Variable loc) 
  in  dcont env' sto'

-- elaborate (Funcdef(name, fp, e)) env dcont sto =
--   let func arg sto' = evaluate e (overlay (parenv, env)) sto'
--                     where parenv = bindParameter fp arg
--       env' = bind(name, Function func)
--   in dcont env' sto

----------------------------------------------------------------------
---------------------------         ----------------------------------
--------------------------- TESTING ----------------------------------
---------------------------         ----------------------------------
----------------------------------------------------------------------
-- ---------- Initialize system  ----------
env_null :: Environ
env_null =  \i -> Unbound

--  store_null =  empty (=0), addressing starts at 1
sto_init :: DataStore
sto_init =  \loc -> Unused

sto_null :: Store
sto_null =  Store( 1, 0, sto_init)

-- dump sto@(Store (lo, hi, d)) = map (\l -> trace (show l) (fetch(sto, l))) [lo..hi]
dump sto@(Store (lo, hi, d)) = fetch(sto, 1)

pgm1 = Letin ( Vardef ("x", Int), Assign("x", Num(3)))

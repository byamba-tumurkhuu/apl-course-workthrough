-----------------------------------------------------------------------------
--
-- Byambatsogt Tumurkhuu
-- 982768
--
-- Module      ::  DSemImp
-- Denotation Semantics Continuation
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
module DSemContImp where

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
               | DoubleAssign(Ident, Ident, Expression, Expression)
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
                  | Funcall (Ident,       ActualParameter)
                  deriving Show

data Declaration = Constdef  (Ident,  Expression) 
                   | Vardef  (Ident,  TypeDef) 
                   | Funcdef (Ident,  FormalParameter, Expression)
                   | Procdef (Ident,  FormalParameter, Command)
                   | Alias   (Ident, Ident)
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

type FunctionType   = Argument -> ExpressionCont -> Store -> Value
type ProcedureType  = Argument -> CommandCont    -> Store -> Value

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

evaluate (Funcall(ident, param)) env econt sto =
  let econt' arg = func arg econt sto
                   where Function func = find(env, ident)
  in  giveArgument param env econt' sto

evaluate ( Leten(dec, e) ) env econt sto =
  let dcont = \env' -> \sto' -> evaluate e (overlay(env', env)) econt sto'
  in  elaborate dec env dcont sto

execute ( Skip ) env ccont sto = ccont sto

execute (Assign(name, exp) ) env ccont sto = 
  let Variable loc = find(env, name)
      econt = \storable -> ccont (update(sto, loc, storable))
  in  evaluate exp env econt sto

execute (DoubleAssign (name1, name2, exp1, exp2)) env ccont sto = 
  let ccont' = execute (Assign(name2, exp2)) env ccont
  in  execute (Assign(name1, exp1)) env ccont' sto


execute (Cmdcmd(c1, c2)) env ccont sto =
  let ccont' = execute c2 env ccont
  in  execute c1 env ccont' sto

execute (Ifthen(e, c1, c2)) env ccont sto = 
  let econt = \b -> if b == TruthValue True
                    then execute c1 env ccont sto
                    else execute c2 env ccont sto
  in evaluate e env econt sto

execute ( Letin(dec, c) ) env ccont sto =
  let dcont = \env' -> \sto' -> execute c (overlay(env', env)) ccont sto'
  in  elaborate dec env dcont sto


execute (Whiledo (e, c) ) env ccont sto = 
  let ccont' sto' = evaluate e env ccont'' sto'
                    where ccont'' = \(TruthValue b) -> if b == True 
                                                       then execute c env ccont' sto' 
                                                       else ccont sto'
  in ccont' sto

execute (Procall(procName, param)) env ccont sto =
  let econt' arg = proc arg ccont sto
                   where Procedure proc = find(env, procName)
  in  giveArgument param env econt' sto

elaborate ( Constdef(name, exp) ) env dcont sto =
  let econt = \v -> dcont (bind(name, Const v)) sto
  in  evaluate exp env econt sto

elaborate (Vardef(name, tdef) ) env dcont sto = 
  let (sto', loc) = allocate sto 
      env' = bind(name, Variable loc) 
  in  dcont env' sto'

elaborate (Funcdef(name, fp, e)) env dcont sto =
  let func arg = evaluate e (overlay (parenv, env))
                 where parenv = bindParameter fp arg
  in  dcont (bind(name, Function func)) sto

elaborate (Procdef(procName, fp, c)) env dcont sto =
  let proc arg = execute c (overlay (parenv, env))
                 where parenv = bindParameter fp arg
  in  dcont (bind(procName, Procedure proc)) sto

elaborate (Alias (id1, id2)) env dcont sto =
  let loc = find(env, id2)
  in dcont (overlay(bind(id1, loc), env)) sto

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

x = Id("x")
y = Id("y")
z = Id("z")
e1 = Num(2)
e2 = Sumof(Num(1), Num(2))
dx = Constdef("x", Num(2))	-- a declaration

dump l sto@(Store (lo, hi, d)) = fetch(sto, l)

pgm1 = Letin( Constdef( "x", Num(2)),
             Letin( Vardef( "y", Int),
                    Cmdcmd( Assign( "y", Num(3)),
                            Ifthen( Less(Id("x"), Id("y")), Assign("y", Num(1)), Assign("y", Num(2)))
                          )
                  )
           )

-------------------------------------------------
--                pgm2
pgm2 = Letin( Constdef( "x", Num(2)),
                        Letin( Vardef(  "y", Int),
                               Cmdcmd( Assign( "y", Num(3)),
                                       Letin ( Vardef( "z", Int),
                                               Cmdcmd( Assign("z", Num(0)), Assign("z", Sumof(z, Num(1))))
                                             )
                                    )
                             )
            )
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
                                                       Assign("y", Subof(y, Num(1)))
                                                      )
                                               )
                                       )
                                 )
                          )
                  )
            )
-------------------------------------------------
--                pgm4
sqr = Id("sqr")
pgm4 = Letin(Constdef( "x", Num(3)),
             Letin( Funcdef("square", FormalParameter("sqr", Int), Prodof(sqr, sqr)),
                    Letin( Vardef( "y", Int),
                           Assign( "y", Funcall("square", ActualParameter x))
                    )
                  )
            )


-------------------------------------------------
--                pgm5
proc = Id("param")
pgm5 = Letin(Constdef("x", Num(5)),
             Letin(Vardef ("y", Int),
                   Cmdcmd (Assign("y", Num(3)),
                           Letin(Procdef("addFive", FormalParameter("param", Int), Assign("y", Sumof(y, proc))),
                                 Procall("addFive", ActualParameter(x))
                                )
                           )
                   )
             )

-------------------------------------------------
--                pgm6
pgm6 = Letin(Vardef("x", Int), Letin (Vardef("y", Int), DoubleAssign( "x", "y", Num(3), Num(5))))

impTests = TestList [ "test evaluate1" ~: (evaluate e1 env_null (\i -> i) sto_null) ~=? (IntValue 2),
                      "test evaluate2" ~: (evaluate e2 env_null (\i -> i) sto_null) ~=? (IntValue 3),
                      "test evaluate3" ~: (evaluate (Sumof(Num(1), Prodof(Num(2), Num(3)))) env_null (\i -> i) sto_null) ~=? (IntValue 7),
                      "test Leten1" ~: (evaluate (Leten(dx, Sumof(Num(1), Id("x")))) env_null (\i -> i) sto_null) ~=? (IntValue 3),
                      "test store1" ~: execute pgm1 env_null (dump 1) sto_null ~=? (IntValue 1),
                      "test store2" ~: execute pgm2 env_null (dump 1) sto_null ~=? (IntValue 3),
                      "test store2" ~: execute pgm2 env_null (dump 2) sto_null ~=? (IntValue 1),
                      "test while1" ~: execute pgm3 env_null (dump 1) sto_null ~=? (IntValue 0),
                      "test while2" ~: execute pgm3 env_null (dump 2) sto_null ~=? (IntValue 6),
                      "test store4" ~: execute pgm4 env_null (dump 1) sto_null ~=? (IntValue 9),
                      "test Procedure" ~: execute pgm5 env_null (dump 1) sto_null ~=? (IntValue 8),
                      "test doublAssignment1" ~: execute pgm6 env_null (dump 1) sto_null ~=? (IntValue 3),
                      "test doublAssignment2" ~: execute pgm6 env_null (dump 2) sto_null ~=? (IntValue 5)
                    ]

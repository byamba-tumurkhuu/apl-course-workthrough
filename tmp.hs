
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
  let doWhile env sto = if evaluate(e) env sto == TruthValue True 
                        then doWhile env (execute(c) env sto)
                        else sto
  in  doWhile env sto

execute (Procall(procName, param)) env sto = 
  let arg =  giveArgument (param) env sto
      proc = case find(env, procName) of
             Procedure p -> p
             _           -> error "Not procedure!"
  in proc arg sto

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


evaluate (Funcall(funcName, param)) env sto =  
  let arg = giveArgument (ActualParameter param) env sto
      func = case find (env, funcName) of
             Function f -> f
             _          -> error "not a function call"
  in  func arg sto

elaborate ( Constdef(name, e) ) env sto =
  let v = evaluate e env sto
  in  ( bind(name, Const  v), sto )

elaborate ( Vardef(name, tdef) ) env sto =
  let (sto', loc) = allocate sto
  in  ( bind(name, Variable loc), sto' )

elaborate (Funcdef(name, fp, e)) env sto =
  let func arg sto' = evaluate (e) (overlay (parenv, env)) sto'
                    where parenv = bindParameter fp arg
  in (bind(name, Function func), sto)

elaborate (Procdef(procName, fp, c)) env sto =
  let proc arg sto' = execute (c) (overlay (parenv, env)) sto'
                    where parenv = bindParameter fp arg
  in (bind(procName, Procedure proc), sto)


----------------------------------------------------------------------
---------------------------         ----------------------------------
--------------------------- TESTING ----------------------------------
---------------------------         ----------------------------------
----------------------------------------------------------------------

dump sto@(Store (lo, hi, d)) = map (\l -> trace (show l) (fetch(sto, l))) [lo..hi]

x = Id("x")
y = Id("y")
z = Id("z")
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

-------------------------------------------------
--                pgm4
sqr = Id("sqr")
pgm4 = Letin(Constdef( "x", Num(3)),
             Letin( Funcdef("square", FormalParameter("sqr", Int), Prodof(sqr, sqr)),
                    Letin( Vardef( "y", Int),
                           Assign( "y", Funcall("square", x))
                    )
                  )
            )

store4 = execute pgm4 env_null sto_null
-------------------------------------------------

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
store5 = execute pgm5 env_null sto_null
-------------------------------------------------

                                    
impTests = TestList [ "test evaluate1" ~: (evaluate e1 env_null sto_null) ~=? (IntValue 2),
                      "test evaluate2" ~: (evaluate e2 env_null sto_null) ~=? (IntValue 3),
                      "test evaluate3" ~: (evaluate (Sumof(Num(1), Prodof(Num(2), Num(3)))) env_null sto_null) ~=? (IntValue 7),
                      "test Leten1" ~: (evaluate (Leten(dx, Sumof(Num(1), Id("x")))) env_null sto_null) ~=? (IntValue 3),
                      "test store1" ~: (fetch(store1, 1)) ~=? (IntValue 1), 
                      "test store2" ~: (fetch(store2, 1)) ~=? (IntValue 3),
                      "test store2" ~: (fetch(store2, 2)) ~=? (IntValue 1),
                      "test store3" ~: (fetch(store3, 1)) ~=? (IntValue 0),
                      "test store3" ~: (fetch(store3, 2)) ~=? (IntValue 6),
                      "test Function" ~: (fetch(store4, 1)) ~=? (IntValue 9),
                      "test Procedure" ~: (fetch(store5, 1)) ~=? (IntValue 8)
                    ]

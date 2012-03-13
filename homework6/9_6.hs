
data Exp = Add Exp Exp | Diff Exp Exp | Mult Exp Exp | Quot Exp Exp | Numb Int 
  deriving (Show)


eval :: Exp -> Int
eval (Numb x) = x
eval (Add  e1 e2) = eval e1 + eval e2
eval (Mult e1 e2) = eval e1 * eval e2
eval (Diff e1 e2) = eval e1 - eval e2
eval (Quot e1 e2) = quot (eval e1)  (eval e2)

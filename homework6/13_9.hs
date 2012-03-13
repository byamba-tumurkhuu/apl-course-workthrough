

repl :: Int -> String -> String
repl n s = concat (replicate n s)

listOr :: [Bool] -> Bool
listOr = foldl (||) False

yieldAsterisk :: [Int] -> String
yieldAsterisk = foldr repl "*"

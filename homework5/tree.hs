data Tree = Empty | Node Int Tree Tree deriving (Show, Eq)

treeInsert newVal Empty = Node newVal Empty Empty 
treeInsert newVal (Node val l r) = if newVal <= val 
                               then Node val (treeInsert newVal l) r
                               else Node val l (treeInsert newVal r)

-- creates a tree from the given list
-- foldl (\t v -> treeInsert v t) Empty xs
listToTree xs = foldl (flip treeInsert) Empty xs

-- Converts a list to tree
treeToList Empty = []
treeToList (Node val l r) = treeToList l ++  val : treeToList r

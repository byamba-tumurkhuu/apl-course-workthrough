
-- i. Count the negatives
countNegatives l = length (filter (\a -> a >= 0) l)


-- ii. Count how often a given string s occurs in a list l.
countString s l = foldl (\x y -> if (y == s) then x + 1 else x) 0 l


-- iii. Construct a list of all the integers in a list l which are greater than a given value v.
construct v l = filter ( > v ) l


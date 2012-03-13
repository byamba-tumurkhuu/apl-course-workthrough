import List

-- i. Triples the given y
tripleMe y = y * y * y


--ii.Find x implies y from x implies y == not x or y given x and y. The function implies should be prefix.
implies x y = (||) (not x) y

-- iii. Smallest of a, b, c
smalllest a b c = min a (min b c)

-- iv. Join strings s1 and s2 together in descending alphabetic order.
joinString s1 s2 = sort (s1 ++ s2)

-- v. Shorter string
shorterString s1 s2 = if (length s1 > length s2) then s2 else s1

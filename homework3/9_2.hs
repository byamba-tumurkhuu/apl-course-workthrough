
-- i. Sum of 1 to n
sumOf n = calcSum 1 n 0
calcSum i n sum = if (i <= n) then calcSum (i+1) n (sum + i) else sum

-- ii. Sum of integers between m and n
sumMN m n = calcSum m n 0


-- iii. Repeat a string s integer n times.
-- Appends the string for n times
repeatString s n = appendString s s n 1
appendString original s n i = if (i < n) then appendString original (s ++ original) n (i + 1) else s

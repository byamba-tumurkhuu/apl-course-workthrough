stock_list = [("RAM",9,10), ("ROM",12,10), ("PROM",20,21)]

-- 9.3 vi) a.construct a list of those stock records with the number in stock less than the reorder level.
check :: [(String, Integer, Integer)] -> [(String, Integer, Integer)]
check = filter (\(a, b, c) -> b <= c) 


-- 9.3 vi) b. update a list of stock records from a list of update records represented as tuples of:
get_for item = filter (( == item) . fst) update_list
  where update_list = [("PROM",15), ("RAM",12), ("PROM",15)]

get_total_for = foldl (+) 0 . map snd . get_for

res = map (\(a, b, c) -> (a, b + (get_total_for a), c)) stock_list 

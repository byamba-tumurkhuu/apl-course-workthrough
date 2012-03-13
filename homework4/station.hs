import List
import Maybe

data Station = Queens_Street | Bishopbriggs | Lenzie | Croy | Polmont | Falkirk_High | Linlithgow | Haymarket | Waverly
  deriving (Eq, Show)


get_neighbor :: String -> Station -> String
get_neighbor "east" Queens_Street = "No station found on the east of : " ++ show Queens_Street
get_neighbor "west" Waverly = "No station found on the west of : " ++ show Waverly 
get_neighbor direction station =
  let station_list = [Queens_Street, Bishopbriggs, Lenzie, Croy, Polmont, Falkirk_High, Linlithgow, Haymarket, Waverly]
      t = elemIndex station station_list
  in
    if isJust t 
    then
      let i = fromJust t
      in
        "Found: " ++ show (station_list !! if direction == "west" then i + 1 else i - 1)
    else 
      "No such station exists"

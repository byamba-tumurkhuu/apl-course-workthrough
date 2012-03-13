f :: Int -> Int -> Int
f a b = a + b


data Customer = Customer {
  customerId :: Int,
  name :: String
} deriving (Show)

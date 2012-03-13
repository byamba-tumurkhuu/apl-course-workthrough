

from :: Integer -> [Integer]
from n = n : from (n + 1)


powerOfTwoLessThan (x:xs) m = if x^2 < m then x else powerOfTwoLessThan xs m

-- isPrime is taken from http://www.haskell.org/haskellwiki/Testing_primality
primes = 2 : filter isPrime [3,5..]
isPrime n = n > 1 && foldr (\p r -> p*p > n || ((n `rem` p) /= 0 && r)) True primes

primeBetween (x:xs) m n primeNums = if x > n then 
                                      primeNums
                                    else 
                                      if x < m || not (isPrime x) then
                                        primeBetween xs m n primeNums
                                      else
                                        primeBetween xs m n (primeNums ++ [x])

                                          
                                        
                                      

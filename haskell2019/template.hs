module SOL where

import Data.List
import Data.Maybe

import Types
import TestData

printF :: Formula -> IO()
printF
  = putStrLn . showF
  where
    showF (Var v)
      = v
    showF (Not f)
      = '!' : showF f
    showF (And f f')
      = "(" ++ showF f ++ " & " ++ showF f' ++ ")"
    showF (Or f f')
      = "(" ++ showF f ++ " | " ++ showF f' ++ ")"

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp k
  = fromJust . (lookup k)

-- 3 marks
vars :: Formula -> [Id]
vars (Var v)
  = [v]
vars (Not f)
  = vars f
vars (And f f')  
  = sort (nub (vars f ++ vars f'))
vars (Or f f')  
  = sort (nub (vars f ++ vars f'))
   
-- 1 mark
idMap :: Formula -> IdMap
idMap
--   = (flip zip) [1..] . vars
  = (`zip` [1..]) . vars
--------------------------------------------------------------------------
-- Part II

-- An encoding of the Or distribution rules.
-- Both arguments are assumed to be in CNF, so the
-- arguments of all And nodes will also be in CNF.
distribute :: CNF -> CNF -> CNF
distribute a (And b c)
  = And (distribute a b) (distribute a c)
distribute (And a b) c
  = And (distribute a c) (distribute b c)
distribute a b
  = Or a b

-- 4 marks
toNNF :: Formula -> NNF
toNNF (Not (Not f))
  = toNNF f
toNNF (Not (And f f'))  
  = Or (toNNF (Not f)) (toNNF (Not f'))
toNNF (Not (Or f f'))  
  = And (toNNF (Not f)) (toNNF (Not f'))
toNNF (And f f')  
  = And (toNNF f) (toNNF f')
toNNF (Or f f')  
  = Or (toNNF f) (toNNF f')
toNNF f
  = f

-- 3 marks
toCNF :: Formula -> CNF
toCNF
  = toCNF' . toNNF

toCNF' :: NNF -> CNF 
toCNF' (Or a b)
  = distribute (toCNF' a) (toCNF' b)
toCNF' (And a b)
  = And (toCNF' a) (toCNF' b)
toCNF' f
  = f

-- 4 marks

flatten :: CNF -> CNFRep
flatten f
  = flatten' f
  where
    ids = idMap f
    flatten' :: CNF -> CNFRep
    flatten' (And f f')
      = flatten' f ++ flatten' f'
    flatten' (Or f f')
      = [concat (flatten' f ++ flatten' f')]
    flatten' (Var a)
      = [[lookUp a ids]]
    flatten' (Not (Var a))
      = [[- lookUp a ids]]

   
--------------------------------------------------------------------------
-- Part III

-- 5 marks
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits f
 = propUnits' f []

propUnits' :: CNFRep -> [Int] -> (CNFRep, [Int])
propUnits' f acc
  | null units = (f, acc)
  | otherwise  = propUnits' (del unit f) (unit : acc)
  where
    units    = [x | [x] <- f]
    unit : _ = units 

del :: Int -> CNFRep -> CNFRep
del _ []
  = []
del n (x:xs)
  | elem n x    = del n xs
  | elem (-n) x = filter (/= -n) x : del n xs
  | otherwise   = x : del n xs


-- 4 marks
dp :: CNFRep -> [[Int]]
dp f
  = dp' f []

dp' :: CNFRep -> [Int] -> [[Int]]
dp' f acc
  | null cnf    = [res]
  | elem [] cnf = [] 
  | otherwise   = dp' ([u] : cnf) res ++ dp' ([- u] : cnf) res
  where
    res          = units ++ acc
    (cnf, units) = propUnits f
    (u:_):_      = cnf

-- n = 8, 9, 10, 11 ...
-- [length sols] = [92,352,724,2680]

--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat f
  = concatMap (map sort . allSat' (idMap f) []) (dp (flatten (toCNF f)))

allSat' :: IdMap -> [(Id, Bool)] -> [Int] -> [[(Id, Bool)]]
allSat' [] acc d
  = [acc]
allSat' ((k,v):ps) acc d
  | elem v d    = t
  | elem (-v) d = f
  | otherwise = t ++ f
  where 
    t = allSat' ps ((k, True):acc) d
    f = allSat' ps ((k, False):acc) d


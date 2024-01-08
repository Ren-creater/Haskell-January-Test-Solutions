module Tries where

import Data.List hiding (insert)
import Data.Bits

import Types
import HashFunctions
import Examples

--------------------------------------------------------------------
-- Part I

-- Use this if you're counting the number of 1s in every
-- four-bit block...
bitTable :: [Int]
bitTable
  = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]

countOnes :: Int -> Int
countOnes n
  = sum (map (bitTable !!) [shiftR n (4 * i) .&. (bit 4 - 1) | i <- [0..15]])

countOnesFrom :: Int -> Int -> Int
countOnesFrom i
  -- = countOnes . ((bit i - 1) .&.)
  = countOnes . (.&.) (bit i - 1)

getIndex :: Int -> Int -> Int -> Int
getIndex n i b
  = shiftR n (b * i) .&. (bit b - 1)

-- Pre: the index is less than the length of the list
replace :: Int -> [a] -> a -> [a]
replace n (x:xs) i
  = case n of
      0 -> i : xs
      _ -> x : replace (n - 1) xs i

-- Pre: the index is less than or equal to the length of the list
insertAt :: Int -> a -> [a] -> [a]
insertAt _ i []
  = [i]
insertAt n i (x:xs)
  = case n of
      0 -> i : x : xs
      _ -> x : insertAt (n - 1) i xs

--------------------------------------------------------------------
-- Part II

sumTrie :: (Int -> Int) -> ([Int] -> Int) -> Trie -> Int
sumTrie f g (Leaf is)
  = g is
sumTrie f g (Node v ns)
  = sum (map (sumSubNode f g) ns)

sumSubNode :: (Int -> Int) -> ([Int] -> Int) -> SubNode -> Int
sumSubNode f g (Term i)
  = f i
sumSubNode f g (SubTrie t)
  = sumTrie f g t

--
-- If you get the sumTrie function above working you can uncomment
-- these three functions; they may be useful in testing.
--
trieSize :: Trie -> Int
trieSize t
  = sumTrie (const 1) length t

binCount :: Trie -> Int
binCount t
  = sumTrie (const 1) (const 1) t

meanBinSize :: Trie -> Double
meanBinSize t
  = fromIntegral (trieSize t) / fromIntegral (binCount t)


member :: Int -> Hash -> Trie -> Int -> Bool
member
  = go 0

go :: Int -> Int -> Hash -> Trie -> Int -> Bool
go _ v _ (Leaf vs) _
  = elem v vs
go l v h (Node vec nodes) b
  -- = case (getIndex vec i 1) of
  --     0 -> False
  --     1 -> case (nodes !! n) of
  --            Term val  -> val == v
  --            SubTrie t -> go (l + 1) v h t b
  | testBit vec i = case (nodes !! n) of
                      Term val  -> val == v
                      SubTrie t -> go (l + 1) v h t b
  | otherwise     = False
  where 
    i = getIndex h l b 
    n = countOnesFrom i vec



--------------------------------------------------------------------
-- Part III

insert :: HashFun -> Int -> Int -> Int -> Trie -> Trie
insert hf maxDepth b v t
  = insert' v 0 t
  where 
    insert' :: Int -> Int -> Trie -> Trie
    insert' v l (Leaf vs)
      = Leaf (union [v] vs)
    insert' v l (Node vec nodes)
      | l == maxDepth -1 = Leaf [v]
      | testBit vec i    = Node vec (replace n nodes insertN)
      | otherwise        = Node (setBit vec i) (insertAt n (Term v) nodes)
      where 
        i = getIndex (hf v) l b
        n = countOnesFrom i vec
        insertN :: SubNode
          = case (nodes !! n) of
              SubTrie tr -> SubTrie (insert' v (l + 1) tr)
              Term v'    -> if v == v' 
                            then Term v'
                            else SubTrie (insert' v (l + 1) (insert' v' (l + 1) empty))


    

buildTrie :: HashFun -> Int -> Int -> [Int] -> Trie
buildTrie hf maxDepth b vs
  = foldr (insert hf maxDepth b) empty vs

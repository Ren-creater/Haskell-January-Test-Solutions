data SuffixTree = Leaf Int | Node [(String, SuffixTree)] 
                deriving (Eq, Show)

------------------------------------------------------

isPrefix :: String -> String -> Bool
isPrefix s a
  = and ((s <= a) : zipWith (==) s a)

removePrefix :: String -> String -> String
removePrefix s
--Pre: s is a prefix of s'
  = drop (length s)

suffixes :: [a] -> [[a]]
suffixes s
  = take (length s) (iterate tail s)

isSubstring :: String -> String -> Bool
isSubstring a s
  = or (map (isPrefix a) (suffixes s))

findSubstrings :: String -> String -> [Int]
findSubstrings s a
  = [ n | n <- [0..length suffs - 1], isPrefix s (suffs!!n)]
  where 
    suffs = suffixes a

------------------------------------------------------

getIndices :: SuffixTree -> [Int]
getIndices (Node xs)
  -- = concatMap match xs
  = concatMap (getIndices . snd) xs
getIndices (Leaf i)
  = [i]


partition :: Eq a => [a] -> [a] -> ([a], [a], [a])
partition s s'
  = (commonPrefix, rest s, rest s')
  where 
    rest         = drop (length commonPrefix)
    commonPrefix = map (\(a,b) -> a) (takeWhile (\(a,b) -> a == b) (zip s s'))

findSubstrings' :: String -> SuffixTree -> [Int]
findSubstrings' s (Node xs)
  = concatMap (\(a, tree) -> byCases (partition s a) tree) xs
findSubstrings' "" (Leaf i)
  = [i]
findSubstrings' _  _
  = []

byCases :: (String, String, String) -> SuffixTree -> [Int]
byCases (p, "", a) tree = getIndices tree
byCases (p, s, "") tree = findSubstrings' s tree
byCases _          _    = []               

-- byCases :: String -> String -> SuffixTree -> [Int]
-- byCases s a tree
--   | isPrefix s a = getIndices tree
--   | isPrefix a s = findSubstrings' (removePrefix a s) tree
--   | otherwise    = []

------------------------------------------------------

insert :: (String, Int) -> SuffixTree -> SuffixTree
insert (s,n) (Node xs)
  = Node (same (s,n) xs (map (\(a, t) -> insertCases (partition s a) n (a,t)) xs))

same :: (String, Int) -> [(String,SuffixTree)] -> [(String, SuffixTree)] -> [(String, SuffixTree)]
same (s,n) xs ys
  | xs == ys  = (s, Leaf n) : xs
  | otherwise = ys

insertCases :: (String, String, String) -> Int -> (String, SuffixTree) -> (String, SuffixTree)
insertCases ("", s, a) _ (l, t) = (l, t)
insertCases (p, s, "") n (l, t) = (l, insert (s, n) t)
insertCases (p, s, a)  n (l, t) = (p, Node [(s, Leaf n), (a, t)]) 


-- This function is given
buildTree :: String -> SuffixTree 
buildTree s
  = foldl (flip insert) (Node []) (zip (suffixes s) [0..])

------------------------------------------------------
-- Part IV

longestRepeatedSubstring :: SuffixTree -> String
longestRepeatedSubstring (Leaf _)
  = []
longestRepeatedSubstring (Node [])
  = []
longestRepeatedSubstring (Node ((a,t):xs))
  | repeated t = longest (a ++ longestRepeatedSubstring t) rest
  | otherwise = rest
  where 
    rest = longestRepeatedSubstring (Node xs)

longest :: String -> String -> String
longest a b
  | length a > length b = a
  | otherwise           = b

repeated :: SuffixTree -> Bool
repeated (Node (_:_:_)) = True
repeated _              = False 

------------------------------------------------------
-- Example strings and suffix trees...

s1 :: String
s1 
  = "banana"

s2 :: String
s2 
  = "mississippi"

t1 :: SuffixTree
t1 
  = Node [("banana", Leaf 0), 
          ("a", Node [("na", Node [("na", Leaf 1), 
                                   ("", Leaf 3)]), 
                     ("", Leaf 5)]), 
          ("na", Node [("na", Leaf 2), 
                       ("", Leaf 4)])]

t2 :: SuffixTree
t2 
  = Node [("mississippi", Leaf 0), 
          ("i", Node [("ssi", Node [("ssippi", Leaf 1), 
                                    ("ppi", Leaf 4)]), 
                      ("ppi", Leaf 7), 
                      ("", Leaf 10)]), 
          ("s", Node [("si", Node [("ssippi", Leaf 2), 
                                   ("ppi", Leaf 5)]), 
                      ("i", Node [("ssippi", Leaf 3), 
                                  ("ppi", Leaf 6)])]), 
          ("p", Node [("pi", Leaf 8), 
                      ("i", Leaf 9)])]



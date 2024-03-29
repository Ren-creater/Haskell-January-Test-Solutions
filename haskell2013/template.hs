type BinHeap a = [BinTree a]

data BinTree a = Node a Int (BinHeap a)
               deriving (Eq, Ord, Show)

--------------------------------------------------------------
-- PART I

key :: BinTree a -> a
key
  = undefined

value :: BinTree a -> a
value (Node a _ _)
  = a

rank :: BinTree a -> Int
rank (Node _ r _)
  = r

children :: BinTree a -> [BinTree a]
children (Node _ _ c)
  = c

combineTrees :: Ord a => BinTree a -> BinTree a -> BinTree a
combineTrees t1@(Node a1 r c1) t2@(Node a2 _ c2)
  | a1 < a2   = Node a1 (r+1) (t2:c1)
  | otherwise = Node a2 (r+1) (t1:c2)

--------------------------------------------------------------
-- PART II

extractMin :: Ord a => BinHeap a -> a
extractMin 
  = minimum . map value

mergeHeaps :: Ord a => BinHeap a -> BinHeap a -> BinHeap a
mergeHeaps [] h'
  = h'
mergeHeaps h []
  = h
mergeHeaps h@(t:ts) h'@(t':ts')
  | rank t < rank t' = t : mergeHeaps ts h'
  | rank t > rank t' = t' : mergeHeaps h ts'
  | otherwise  = mergeHeaps [combineTrees t t'] (mergeHeaps ts ts')

insert :: Ord a => a -> BinHeap a -> BinHeap a
insert a
  = mergeHeaps [Node a 0 []] 

deleteMin :: Ord a => BinHeap a -> BinHeap a
deleteMin []
  = []
deleteMin h
  = remove min h
  where
    min = extractMin h

remove :: Ord a => a -> BinHeap a -> BinHeap a
-- Pre: a tree with root value a exists in the heap
remove a (t : ts)
  | a == value t = mergeHeaps (reverse (children t)) ts
  | otherwise    = mergeHeaps [t] (remove a ts)

binSort :: Ord a => [a] -> [a]
binSort 
  = toList . foldr insert []

toList :: Ord a => BinHeap a -> [a]
toList [] 
  = []
toList h
  = deleteMin h : toList (extractMin h)

--------------------------------------------------------------
-- PART III

toBinary :: BinHeap a -> [Int]
toBinary
  = toB . binSort . map rank

toB :: [Int] -> [Int]
toB rs
  = reverse [if elem r rs then 1 else 0 | r <- [0..(last rs)]]

binarySum :: [Int] -> [Int] -> [Int]
binarySum a b
  = reverse (binarySum' (reverse a) (reverse b) 0)

  where
    binarySum' :: [Int] -> [Int] -> Int -> [Int]
    binarySum' [] [] c
      | c == 0 = []
      | otherwise = [1]
    binarySum' [] b c
      = binarySum' [0] b c
    binarySum' a [] c
      = binarySum' a [0] c
    binarySum' (a:as) (b:bs) c
      = s : binarySum' as bs c'
      where
        (c',s) = quotRem (a + b + c) 2


------------------------------------------------------
-- Some sample trees...

t1, t2, t3, t4, t5, t6, t7, t8 :: BinTree Int
-- Note: t7 is the result of merging t5 and t6

-- t1 to t4 appear in Figure 1...
t1 = Node 4 0 []
t2 = Node 1 1 [Node 5 0 []]
t3 = Node 2 2 [Node 8 1 [Node 9 0 []], 
               Node 7 0 []]
t4 = Node 2 3 [Node 3 2 [Node 6 1 [Node 8 0 []], 
                         Node 10 0 []],
               Node 8 1 [Node 9 0 []],
               Node 7 0 []]

-- t5 and t6 are on the left of Figure 2; t7 is on the
-- right
t5 = Node 4 2 [Node 6 1 [Node 8 0 []], 
                         Node 10 0 []]
t6 = Node 2 2 [Node 8 1 [Node 9 0 []], Node 7 0 []]
t7 = Node 2 3 [Node 4 2 [Node 6 1 [Node 8 0 []], Node 10 0 []],
               Node 8 1 [Node 9 0 []], 
               Node 7 0 []]

-- An additional tree...
t8 = Node 12 1 [Node 16 0 []]

------------------------------------------------------
-- Some sample heaps...

h1, h2, h3, h4, h5, h6, h7 :: BinHeap Int
-- Two arbitrary heaps for testing...
h1 = [t2, t7]
h2 = [Node 1 2 [Node 12 1 [Node 16 0 []],
                Node 5 0 []],
      Node 2 3 [Node 4 2 [Node 6 1 [Node 8 0 []],
                          Node 10 0 []],
                Node 8 1 [Node 9 0 []],
                Node 7 0 []]]

-- h3 is shown in Figure 3...
h3 = [t1, t2, t4]

-- Two additional heaps, used below. They are shown
-- in Figure 4(a)...

h4 = [t2, t5]
h5 = [t1, t8]

-- h6 is the result of merging h4 and h5, shown in Figure 4(b)...
h6 = [Node 4 0 [],
      Node 1 3 [Node 4 2 [Node 6 1 [Node 8 0 []],
                          Node 10 0 []],
                Node 12 1 [Node 16 0 []],
                Node 5 0 []]]

-- h7 is shown in Figure 5...
h7 = [Node 4 3 [Node 4 2 [Node 12 1 [Node 16 0 []],
                          Node 5 0 []],
                Node 6 1 [Node 8 0 []],
                Node 10 0 []]]

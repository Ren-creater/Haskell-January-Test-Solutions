import Data.List

type Index = Int

data BExp = Prim Bool | IdRef Index | Not BExp | And BExp BExp | Or BExp BExp
            deriving (Eq, Ord, Show)

type Env = [(Index, Bool)]

type NodeId = Int

type BDDNode =  (NodeId, (Index, NodeId, NodeId))

type BDD = (NodeId, [BDDNode])

------------------------------------------------------
-- PART I

-- Pre: The item is in the given table
lookUp :: Eq a => a -> [(a, b)] -> b
lookUp x l
  = head [v | (k,v) <- l, x == k]

checkSat :: BDD -> Env -> Bool
checkSat (root, nodes) env
  | root == 1    = True
  | root == 0    = False
  | varState     = checkSat (itr, nodes) env
  | not varState = checkSat (ifa, nodes) env
  where
    initial@(ivar, ifa, itr) = lookUp root nodes
    varState                 = lookUp ivar env

sat :: BDD -> [[(Index, Bool)]]
sat (root, nodes)
  | root == 1 = [[]]
  | root == 0 =  []
  | otherwise = itrReturn ++ ifaReturn
  where
    initial@(ivar, ifa, itr) = lookUp root nodes
    itrReturn = map ((ivar, True) :) (sat (itr, nodes))
    ifaReturn = map ((ivar, False):) (sat (ifa, nodes))


------------------------------------------------------
-- PART II

simplify :: BExp -> BExp
simplify (Not (Prim bool))
  = Prim (not bool)
simplify (And (Prim b1) (Prim b2))
  = Prim (b1 && b2)
simplify (Or (Prim b1) (Prim b2))
  = Prim (b1 || b2)
simplify e
  = e

restrict :: BExp -> Index -> Bool -> BExp
restrict e@(IdRef ind) i bool
  | i == ind   = Prim bool
  | otherwise = e 
restrict (Not e) i bool     
  = simplify (Not (restrict e i bool))
restrict (Or e1 e2) i bool
  = simplify (Or (restrict e1 i bool) (restrict e2 i bool))
restrict (And e1 e2) i bool
  = simplify (And (restrict e1 i bool) (restrict e2 i bool))
restrict (Prim e) _ _    
  = Prim e

------------------------------------------------------
-- PART III

-- Pre: Each variable index in the BExp appears exactly once
--     in the Index list; there are no other elements
-- The question suggests the following definition (in terms of buildBDD')
-- but you are free to implement the function differently if you wish.
buildBDD :: BExp -> [Index] -> BDD
buildBDD
  = flip buildBDD' 2

-- Potential helper function for buildBDD which you are free
-- to define/modify/ignore/delete/embed as you see fit.
buildBDD' :: BExp -> NodeId -> [Index] -> BDD
-- buildBDD' e i []
--   = (eval, [])
--   where 
--     eval = case e of 
--              Prim True -> 1
--              _         -> 0
buildBDD' (Prim True) i []
  = (1, [])
buildBDD' (Prim False) i []
  = (0, [])
buildBDD' e i (x:xs)
  = (i, (i,(x,li,ri)) : l ++ r)
  where 
    (li, l) = buildBDD' (restrict e x False) (i * 2) xs
    (ri, r) = buildBDD' (restrict e x True) (i * 2 + 1) xs

------------------------------------------------------
-- PART IV

-- Pre: Each variable index in the BExp appears exactly once
--      in the Index list; there are no other elements
buildROBDD :: BExp -> [Index] -> BDD
buildROBDD b inds
  = buildROBDD' b 2 inds []

buildROBDD' :: BExp -> NodeId -> [Index] -> [BDDNode] -> BDD
buildROBDD' (Prim True) i [] nodes
  = (1, [])
buildROBDD' (Prim False) i [] nodes
  = (0, [])
buildROBDD' e i (x:xs) nodes
  = case nodeElem nn nodes of
      Nothing -> case lind == rind of
                   True  -> (li, l)
                   False -> (i, nn : l ++ r)
      Just ni -> (ni, [])
  where
    nn           = (i, (x,li,ri))
    (lind, _, _) = lookUp li l
    (rind, _, _) = lookUp ri r 
    (li, l)      = buildROBDD' (restrict e x False) (i*2) xs nodes
    (ri, r)      = buildROBDD' (restrict e x True) (i*2+1) xs (union nodes l)

nodeElem :: BDDNode -> [BDDNode] -> Maybe NodeId
nodeElem _ []
  = Nothing
nodeElem nn@(_, (x,li,ri)) ((ni,(nx,nli,nri)):ns)
  | x == nx && li == nli
            && ri == nri = Just ni
  | otherwise            = nodeElem nn ns


------------------------------------------------------
-- Examples for testing...

b1, b2, b3, b4, b5, b6, b7, b8 :: BExp
b1 = Prim False
b2 = Not (And (IdRef 1) (Or (Prim False) (IdRef 2)))
b3 = And (IdRef 1) (Prim True)
b4 = And (IdRef 7) (Or (IdRef 2) (Not (IdRef 3)))
b5 = Not (And (IdRef 7) (Or (IdRef 2) (Not (IdRef 3))))
b6 = Or (And (IdRef 1) (IdRef 2)) (And (IdRef 3) (IdRef 4))
b7 = Or (Not (IdRef 3)) (Or (IdRef 2) (Not (IdRef 9)))
b8 = Or (IdRef 1) (Not (IdRef 1))

bdd1, bdd2, bdd3, bdd4, bdd5, bdd6, bdd7, bdd8 :: BDD
bdd1 = (0,[])
bdd2 = (2,[(4,(2,1,1)),(5,(2,1,0)),(2,(1,4,5))])
bdd3 = (5,[(5,(1,0,1))])
bdd4 = (2,[(2,(2,4,5)),(4,(3,8,9)),(8,(7,0,1)),(9,(7,0,0)),
           (5,(3,10,11)),(10,(7,0,1)),(11,(7,0,1))])
bdd5 = (3,[(4,(3,8,9)),(3,(2,4,5)),(8,(7,1,0)),(9,(7,1,1)),
           (5,(3,10,11)),(10,(7,1,0)),(11,(7,1,0))])
bdd6 = (2,[(2,(1,4,5)),(4,(2,8,9)),(8,(3,16,17)),(16,(4,0,0)),
           (17,(4,0,1)),(9,(3,18,19)),(18,(4,0,0)),(19,(4,0,1)),
           (5,(2,10,11)),(10,(3,20,21)),(20,(4,0,0)),(21,(4,0,1)),
           (11,(3,22,23)),(22,(4,1,1)),(23,(4,1,1))])
bdd7 = (6,[(6,(2,4,5)),(4,(3,8,9)),(8,(9,1,1)),(9,(9,1,0)),
           (5,(3,10,11)),(10,(9,1,1)),(11,(9,1,1))])
bdd8 = (2,[(2,(1,1,1))])



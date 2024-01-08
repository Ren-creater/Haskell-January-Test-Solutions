module Alloc where

import Data.Maybe
import Data.List

import Types
import Examples

------------------------------------------------------
--
-- Part I
--
count :: Eq a => a -> [a] -> Int
count x
  = length . filter (== x)

degrees :: Eq a => Graph a -> [(a, Int)]
degrees (nodes, edges)
  = [ (n, count n list) | n <- nodes]
  where
    list = map fst edges ++ map snd edges

neighbours :: Eq a => a -> Graph a -> [a]
neighbours node (_, edges)
  = [b | (a, b) <- list, a == node]
  where
    list = edges ++ swapAll edges

swapAll :: [(a, b)] -> [(b, a)]
swapAll = map swap

swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

removeNode :: Eq a => a -> Graph a -> Graph a
removeNode node (nodes, edges) 
  = (delete node nodes, filter (\(a, b) -> a /= node && b /= node) edges)

------------------------------------------------------
--
-- Part II
--
colourGraph :: (Ord a, Show a) => Int -> Graph a -> Colouring a
colourGraph _ ([], _)
  = []
colourGraph bigC g
  = (n, c) : cMap
  where 
    n    = (snd . minimum . swapAll . degrees) g
    g'   = removeNode n g
    cMap = colourGraph bigC g'
    cs   = map (flip lookUp cMap) (neighbours n g)
    c    = head (([1..bigC] \\ cs) ++ [0])
------------------------------------------------------
--
-- Part III
--
buildIdMap :: Colouring Id -> IdMap
buildIdMap 
  = (("return", "return") :) . map buildIdMap'

buildIdMap' :: (Id, Colour) -> (Id, Id)
buildIdMap' (v, 0)
  = (v, v)
buildIdMap' (v, n)
  = (v, 'R' : show n) 

buildArgAssignments :: [Id] -> IdMap -> [Statement]
buildArgAssignments vs idMap
  = [ Assign (lookUp v idMap) (Var v) | v <- vs] 

renameExp :: Exp -> IdMap -> Exp
-- Pre: A precondition is that every variable referenced in 
-- the expression is in the idMap. 
renameExp (Var id) idMap
  = Var (lookUp id idMap)
renameExp (Apply op e1 e2) idMap
  =  Apply op (renameExp e1 idMap) (renameExp e2 idMap)
renameExp e _
  = e

renameBlock :: Block -> IdMap -> Block
-- Pre: A precondition is that every variable referenced in 
-- the block is in the idMap. 
renameBlock b idMap
  = filter match (map renameStatement b)
  where
    renameStatement :: Statement -> Statement
    renameStatement (Assign id e)
      = Assign (lookUp id idMap) (renameExp e idMap)
    renameStatement (If pe qb rb)
      = If (renameExp pe idMap) (renameBlock qb idMap) (renameBlock rb idMap)
    renameStatement (While e b)
      = While (renameExp e idMap) (renameBlock b idMap)

match :: Statement -> Bool
match (Assign v (Var v')) = not (v == v')   
match _
  = True

renameFun :: Function -> IdMap -> Function
renameFun (f, as, b) idMap
  = (f, as, buildArgAssignments as idMap ++ renameBlock b idMap)

-----------------------------------------------------
--
-- Part IV
--
buildIG :: [[Id]] -> IG
buildIG vss
  = (vars, (nub . map order . filter checkPair) result)
  where
    result = [(v, v') | v <- vars, v' <- vars, vs <- vss, elem v vs && elem v' vs]
    vars   = nub (concat vss)
    order (n, n') = (min n n', max n n')

checkPair :: Eq a => (a, a) -> Bool
checkPair (v, v')
  | v == v'   = False
  | otherwise = True 

-----------------------------------------------------
--
-- Part V
--

liveVars :: CFG -> [[Id]]
liveVars cfg
  = lives initial
  where 
    initial = replicate (length cfg) []    
    lives :: [[Id]] -> [[Id]]
    lives l 
      | l == l'   = l
      | otherwise = lives l'
      where
        l' = map live cfg
        live :: ((Id, [Id]), [Int]) -> [Id]
        live ((def, use), succ)
          = use `union` ((unionAll (map (l !!) succ)) \\ [def])

unionAll :: Eq a => [[a]] -> [a]
unionAll 
  = foldr union []

buildCFG :: Function -> CFG
buildCFG (_, _, b)
  = buildCFG' b 0


buildCFG' :: Block -> Int -> [((Id, [Id]), [Int])]
buildCFG' [] n
  = []
buildCFG' ((Assign id e) : b) n
  = result : buildCFG' b (n + 1)
  where 
    result  = ((id, findVars e), next)
    next    = checkReturn id [n + 1]
buildCFG' (If pe qb rb : b) n
  = (("_", findVars pe), [n + 1, n + blockLength qb + 1]) 
  : qbResult ++ rb' ++ buildCFG' b final
  where
    qbResult           = case qb of 
                           [] -> [] 
                           _  -> init qb' ++ [qb'']
    qb''               = (pQB, checkReturn idQB [final])
    (pQB@(idQB, _), _) = last qb' 
    qb'                = buildCFG' qb (n + 1)
    rb'                = buildCFG' rb (n + 1 + blockLength qb)
    final              = n + blockLength qb + blockLength rb + 1
buildCFG' (While e db : b) n 
  = (("_", findVars e), [n + 1, final])
   : dbResult ++ buildCFG' b final
  where
    dbResult           = case db of
                           [] -> []
                           _  -> init db' ++ [db'']
    db''               = (pDB, checkReturn idDB [n])
    (pDB@(idDB, _), s) = last db' 
    db'                = buildCFG' db (n + 1)
    final              = n + blockLength db + 1

findVars :: Exp -> [Id]
findVars (Var id)
  = [id]
findVars (Apply _ e1 e2 )
  = findVars e1 `union` findVars e2
findVars _
  = []

checkReturn :: Id -> [Int] -> [Int]
checkReturn "return" s 
  = []
checkReturn _        s
  = s

blockLength :: Block -> Int
blockLength
  = sum . map statementLength

statementLength :: Statement -> Int
statementLength (If _ qb rb)
  = 1 + blockLength (qb ++ rb)
statementLength (While _ db)
  = 1 + blockLength db
statementLength _
  = 1

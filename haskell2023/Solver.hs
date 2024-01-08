module Solver where

import Data.List
import Data.Char

import Types
import WordData
import Clues
import Examples

------------------------------------------------------
-- Part I

punctuation :: String
punctuation 
  = "';.,-!?"

cleanUp :: String -> String
cleanUp []
  = []
cleanUp (c:cs) 
  | elem c punctuation = cleanUp cs
  | otherwise          = toLower c : cleanUp cs

split2 :: [a] -> [([a], [a])]
split2 l
  = [splitAt i l | i <- [1..length l - 1]]

split3 :: [a] -> [([a], [a], [a])]
split3
  = concatMap split3' . split2

split3' :: ([a], [a]) -> [([a], [a], [a])]
split3' (a, b)
  = map (\(x, y) -> (a, x, y)) l
  where l = [splitAt i b | i <- [0..length b - 1]]

uninsert :: [a] -> [([a], [a])]
uninsert
  = map uninsert' . filter (\(_, b, _) -> not (null b)). split3

uninsert' :: ([a], [a], [a]) -> ([a], [a])
uninsert' (a, b, c)  = (b, a ++ c)

-- Uncomment these functions when you have defined the above.
split2M :: [a] -> [([a], [a])]
split2M xs
  = sxs ++ [(y, x) | (x, y) <- sxs] 
  where
    sxs = split2 xs

split3M :: [a] -> [([a], [a], [a])]
split3M xs
  = sxs ++ [(z, y, x) | (x, y, z) <- sxs]
  where
    sxs = split3 xs


------------------------------------------------------
-- Part II

matches :: String -> ParseTree -> Bool
matches s (Synonym s')
  = elem s (synonyms s')
matches s (Anagram _ s')
  = sort s == sort s'
matches s (Reversal _ t)
  = matches (reverse s) t
matches s (Insertion _ t1 t2)
  =  matches' t1 t2 (uninsert s)
matches s (Charade _ t1 t2)
  = matches' t1 t2 (split2 s)
matches s (HiddenWord _ s')
  = case s'' of    
      [x] -> elem s [drop j (take i x)
                     | i <- [1..length h - 1],
                       j <- [1..length l - 1]]
      _   -> elem s [drop i h ++ concat (init (tail s'')) ++ take j l
                     | i <- [1..length h - 1],
                       j <- [1..length l - 1]]
  where
    s'' = words s'
    h   = head s''
    l   = last s''

matches' :: ParseTree -> ParseTree-> [(String, String)] -> Bool
matches' t1 t2 = or . map (\(s1, s2) -> matches s1 t1 && matches s2 t2)

evaluate :: Parse -> Int -> [String]
evaluate (def, _, t) n
  = filter ((== n). length) [s | s <- ss, matches s t]
  where 
    ss = synonyms (unwords def)

------------------------------------------------------
-- Part III

-- Given...
parseWordplay :: [String] -> [ParseTree]
parseWordplay ws
  = concat [parseSynonym ws,
            parseAnagram ws,
            parseReversal ws,
            parseInsertion ws,
            parseCharade ws,
            parseHidden ws]
    
parseSynonym :: [String] -> [ParseTree]
parseSynonym ws
  | null (synonyms ws') = []
  | otherwise           = [Synonym ws']
  where
    ws' = unwords ws

parseAnagram :: [String] -> [ParseTree]
parseAnagram
  = concatMap inspect . split2M
  where
    inspect :: ([String], [String]) -> [ParseTree]
    inspect (a, b)
      | elem str anagramIndicators = [Anagram a arg]
      | otherwise                  = []
      where
        str = unwords a
        arg = concat b
  

parseReversal :: [String] -> [ParseTree]
parseReversal
  = concatMap inspect . split2M
  where
    inspect :: ([String], [String]) -> [ParseTree]
    inspect (a, b)
      | elem str reversalIndicators = fmap (Reversal a) (parseWordplay b)
      | otherwise                   = []
      where
        str = unwords a
        

parseInsertion :: [String] -> [ParseTree]
parseInsertion
  = concatMap inspect . split3
  where
    inspect :: ([String], [String], [String]) -> [ParseTree]
    inspect (arg, ws, arg')
      | elem str envelopeIndicators  = [Insertion ws t2 t1 | t1 <- parseWordplay arg, 
                                                             t2 <- parseWordplay arg']
      | elem str insertionIndicators = [Insertion ws t1 t2 | t1 <- parseWordplay arg, 
                                                             t2 <- parseWordplay arg']
      | otherwise                    = []
      where
        str = unwords ws 

parseCharade :: [String] -> [ParseTree]
parseCharade
  = concatMap inspect . split3
  where
    inspect :: ([String], [String], [String]) -> [ParseTree]
    inspect (arg, ws, arg')
      | elem str afterIndicators  = [Charade ws t2 t1 | t1 <- parseWordplay arg, 
                                                             t2 <- parseWordplay arg']
      | elem str beforeIndicators = [Charade ws t1 t2 | t1 <- parseWordplay arg, 
                                                             t2 <- parseWordplay arg']
      | otherwise                 = []
      where
        str = unwords ws 

parseHidden :: [String] -> [ParseTree]
parseHidden
  = concatMap inspect . split3M
  where
    inspect :: ([String], [String], [String]) -> [ParseTree]
    inspect (arg, ws, _)
      | elem str hiddenWordIndicators = [HiddenWord ws (unwords arg)] 
      | otherwise                     = []
      where
        str = unwords ws 

-- Given...
parseClue :: Clue -> [Parse]
parseClue clue@(s, n)
  = parseClueText (words (cleanUp s))

parseClueText :: [String] -> [Parse]
parseClueText
  = concatMap parseClueText' . split3M

parseClueText' :: ([String], [String], [String]) -> [Parse]
parseClueText' (def, link, t)
  | elem link' linkWords = if null (synonyms def')
                            then []
                            else map (\x -> (def, link, x)) (parseWordplay t)
  | otherwise            = []
  where
    link' = unwords link
    def'  = unwords def


solve :: Clue -> [Solution]
solve clue@(s, n)
  = concatMap solve' (parseClue clue)
  where
    solve' :: Parse -> [Solution]
    solve' parse
     | null sol  = []
     | otherwise = map (\s -> (clue, parse, s)) sol
     where
      sol = evaluate parse n


------------------------------------------------------
-- Some additional test functions

-- Returns the solution(s) to the first k clues.
-- The nub removes duplicate solutions arising from the
-- charade parsing rule.
solveAll :: Int -> [[String]]
solveAll k
  = map (nub . map getSol . solve . (clues !!)) [0..k-1]

getSol :: Solution -> String
getSol (_, _, sol) = sol

showAll
  = mapM_ (showSolutions . solve . (clues !!)) [0..23]



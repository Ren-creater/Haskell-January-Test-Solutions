module SC where

import Data.List
import Data.Maybe

import Types
import Examples

---------------------------------------------------------

prims :: [Id]
prims
  = ["+", "-", "*", "<=", "ite"]

lookUp :: Id -> [(Id, a)] -> a
lookUp v env
  = fromMaybe (error ("lookUp failed with search key " ++ v))
              (lookup v env)

---------------------------------------------------------
-- Part I

isFun :: Exp -> Bool
isFun (Fun _ _)
  = True
isFun _
  = False

splitDefs :: [Binding] -> ([Binding], [Binding])
splitDefs 
  = partition (isFun . snd)

topLevelFunctions :: Exp -> Int
topLevelFunctions (Let bs _ )
  = length (filter (isFun . snd) bs) 
topLevelFunctions _
  = 0
---------------------------------------------------------
-- Part II

unionAll :: Eq a => [[a]] -> [a]
unionAll
  = foldr union []

freeVars :: Exp -> [Id]
freeVars (Const _)
  = [] 
freeVars (Var id)
  | elem id prims = [] 
  | otherwise     = [id]
freeVars (App f es)
  = unionAll (map freeVars (f : es))
freeVars (Fun ids e)
  = freeVars e \\ ids
freeVars (Let bs e)
  =  unionAll (map freeVars (e : es)) \\ map fst bs
  where 
    es = map snd bs
---------------------------------------------------------
-- Part III

-- Given...
lambdaLift :: Exp -> Exp
lambdaLift e
  = lift (modifyFunctions (buildFVMap e) e)

buildFVMap :: Exp -> [(Id, [Id])]
buildFVMap e@(Let bs e') 
  = map (\(id, ids) -> (id, ids \\ fids)) fvs'
  where 
    (fbs, _)    = splitDefs bs
    (fids, fes) = unzip fbs
    fvs         = zip fids (repeat (unionAll (map freeVars fes)))
    fvs'        = unionAll (fvs : map buildFVMap (e' : map snd bs))
buildFVMap (Fun _ e)
  = buildFVMap e
buildFVMap (App e es)
  = concatMap buildFVMap (e : es)
buildFVMap _
  = []

modifyFunctions :: [(Id, [Id])] -> Exp -> Exp
-- Pre: The mapping table contains a binding for every function
-- named in the expression.
modifyFunctions m (Let ((f, Fun as ef) : bs) e) 
  = Let (('$' : f, Fun (vs ++ as) ef') : bs') e'
  where 
    vs         = lookUp f m
    Let bs' e' = modifyFunctions m (Let bs e)
    ef'        = modifyFunctions m ef
modifyFunctions m (Let [] e)
  = Let [] (modifyFunctions m e)
modifyFunctions m (Let ((id, exp) : bs) e) 
  = Let ((id, exp') : bs') e'
  where 
    exp'       = modifyFunctions m exp 
    Let bs' e' = modifyFunctions m (Let bs e)
modifyFunctions m e@(Var f)
  | elem f (map fst m) = case lookUp f m of 
                           [] -> Var f'
                           vs -> App (Var f') (fmap Var vs)
  | otherwise          = e
  where 
    f' = '$' : f
modifyFunctions m (App e es)
  = App (modifyFunctions m e) (map (modifyFunctions m) es)
modifyFunctions _ e
  = e 

-- The default definition here is id.
-- If you implement the above two functions but not this one
-- then lambdaLift above will remove all the free variables
-- in functions; it just won't do any lifting.
lift :: Exp -> Exp
lift e
  | null bs   = e'
  | otherwise = Let bs e'
  where
    (e', bs) = lift' e

-- You may wish to use this...
lift' :: Exp -> (Exp, [Supercombinator])
lift' (Let bs e)
  = (result, unionAll [fbs, fbs', bs'])
  where
    result = case vbs of 
               [] -> e'
               _  -> Let vbs e'
    (e', bs')  = lift' e
    list       = [(id, lift' e) | (id, e) <- bs]
    bs''       = map (\(id, (e, _)) -> (id, e)) list
    (fbs, vbs) = splitDefs bs''
    fbs'       = unionAll (map (snd . snd) list)
lift' (Fun as e)
  = (Fun as e', bs) 
  where 
    (e', bs) = lift' e
lift' (App f es)
  = (App f' es', unionAll [bsf, unionAll bse])
  where 
    (f', bsf)  = lift' f
    (es', bse) = unzip (map lift' es)
lift' e
  = (e, [])
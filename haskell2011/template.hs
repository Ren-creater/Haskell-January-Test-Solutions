import Data.Maybe

data Expr = Number Int |
            Boolean Bool |
            Id String  |
            Prim String |
            Cond Expr Expr Expr |
            App Expr Expr |
            Fun String Expr
          deriving (Eq, Show)

data Type = TInt |
            TBool |
            TFun Type Type |
            TVar String |
            TErr
          deriving (Eq, Show)

showT :: Type -> String
showT TInt  
  = "Int"
showT TBool
  = "Bool"
showT (TFun t t')
  = "(" ++ showT t ++ " -> " ++ showT t' ++ ")"
showT (TVar a)
  = a
showT TErr  
  = "Type error"

type TypeTable = [(String, Type)]

type TEnv 
  = TypeTable    -- i.e. [(String, Type)]

type Sub 
  = TypeTable    -- i.e. [(String, Type)]  

-- Built-in function types...
primTypes :: TypeTable
primTypes
  = [("+", TFun TInt (TFun TInt TInt)),
     (">", TFun TInt (TFun TInt TBool)),
     ("==", TFun TInt (TFun TInt TBool)),
     ("not", TFun TBool TBool)]

------------------------------------------------------
-- PART I

-- Pre: The search item is in the table
lookUp :: Eq a => a -> [(a, b)] -> b
lookUp a l
  = tryToLookUp a undefined l

tryToLookUp :: Eq a => a -> b -> [(a, b)] -> b
tryToLookUp a b l
  = head [v | (i, v) <- l', i == a]
  where
    l' = l ++ [(a, b)]  


-- Pre: The given value is in the table
reverseLookUp :: Eq b => b -> [(a, b)] -> [a]
reverseLookUp b l
  = [i | (i, v) <- l, v == b]

occurs :: String -> Type -> Bool
occurs s (TFun t t')
  = occurs s t || occurs s t'
occurs s (TVar s')
  = s == s'
occurs _ _
  = False

------------------------------------------------------
-- PART II

-- Pre: There are no user-defined functions (constructor Fun)
-- Pre: All variables in the expression have a binding in the given
--      type environment
inferType :: Expr -> TEnv -> Type
inferType (Number _) _
  = TInt
inferType (Boolean _) _
  = TBool
inferType (Id i) env
  = lookUp i env
inferType (Prim s) _
  = lookUp s primTypes
inferType (Cond p q r) env
  | violates  = TErr
  | otherwise = tp
  where
    violates = or [tp /= TBool, any (== TErr) ts, tq /= tr]
    ts@[tp, tq, tr] = map (flip inferType env) [p, q, r]
inferType (App f a) env
  = inferApp tf ta
  where 
    tf = inferType f env
    ta = inferType a env

inferApp :: Type -> Type -> Type
inferApp f a    
  | TFun t t' <- f, t == a = t'
  | otherwise              = TErr

------------------------------------------------------
-- PART III

applySub :: Sub -> Type -> Type
applySub s (TFun t t')
  = TFun (applySub s t) (applySub s t')
applySub s (TVar v)
  = tryToLookUp v (TVar v) s
applySub _ t
  = t

unify :: Type -> Type -> Maybe Sub
unify t t'
  = unifyPairs [(t, t')] []

unifyPairs :: [(Type, Type)] -> Sub -> Maybe Sub
unifyPairs [] s
  = Just s
unifyPairs ((TInt, TInt) : p) s
  = unifyPairs p s
unifyPairs ((TBool, TBool) : p) s
  = unifyPairs p s
unifyPairs ((TVar v, t) : p) s
  | TVar v' <- t, v == v' = unifyPairs p s
  | occurs v t            = Nothing
  | otherwise             = unifyPairs p' ((v, t) : s)
  where
    p' = [(applySub [(v, t)] t1, applySub [(v, t)] t2) | (t1, t2) <- p]
unifyPairs ((t, TVar v) : p) s
  = unifyPairs ((TVar v, t) : p) s
unifyPairs ((TFun t1 t2, TFun t1' t2') : p) s
  = unifyPairs ((t1, t1') : (t2, t2') : p) s
unifyPairs _ _
  = Nothing

------------------------------------------------------
-- PART IV

updateTEnv :: TEnv -> Sub -> TEnv
updateTEnv tenv tsub
  = map modify tenv
  where
    modify (v, t) = (v, applySub tsub t)

combine :: Sub -> Sub -> Sub
combine sNew sOld
  = sNew ++ updateTEnv sOld sNew

-- In combineSubs [s1, s2,..., sn], s1 should be the *most recent* substitution
-- and will be applied *last*
combineSubs :: [Sub] -> Sub
combineSubs
  = foldr1 combine

inferPolyType :: Expr -> Type
inferPolyType e
  = t
  where 
    (_, t, _) = inferPolyType' e [] ans

    ans :: [String]
    ans = iterate (\('a' : n) -> 'a' : show (read n + 1)) "a1"

-- You may optionally wish to use one of the following helper function declarations
-- as suggested in the specification.

inferPolyType' :: Expr -> TEnv -> [String] -> (Sub, Type, [String])
inferPolyType' (Fun x e) env (a : ans)
  = (sub, t, ans)
  where 
    t = case te of 
          TErr -> TErr
          _    -> TFun (applySub sub (TVar a)) te
    (sub, te, _) = inferPolyType' e ((x, TVar a) : env) ans
inferPolyType' (App f e) env ans
  = case subu of 
      Nothing -> ([], TErr, ans)
      _       -> (combineSubs [subu', sub2, sub1], applySub subu' (TVar a), ans'')
  where 
    subu'         = fromJust subu
    subu          = unify tf (TFun te (TVar a))
    (sub1, tf, ans') = inferPolyType' f env ans
    (sub2, te, a : ans'') = inferPolyType' e (updateTEnv env sub1) ans'
inferPolyType' (Cond p q r) env ans
  | subu1 == Nothing || subu2 == Nothing = ([], TErr, ans)
  | otherwise                            = (combineSubs [fromJust subu2, fromJust subu1, sub3, sub2, sub1], tq', ans''')
  where
    subu1              = unify tp TBool
    subu2              = unify tq tr 
    (sub1, tp, ans')   = inferPolyType' p env ans
    (sub2, tq, ans'')  = inferPolyType' q (updateTEnv env sub1) ans'
    (sub3, tr, ans''') = inferPolyType' r (updateTEnv env (combineSubs [sub2, sub1])) ans''
    tq'                = applySub subu2 tq
inferPolyType' e env ans
  = ([], inferType e env, ans)

-- inferPolyType' :: Expr -> TEnv -> Int -> (Sub, Type, Int)
-- inferPolyType'
--   = undefined

------------------------------------------------------
-- Monomorphic type inference test cases from Table 1...

env :: TEnv
env = [("x",TInt),("y",TInt),("b",TBool),("c",TBool)]

ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8 :: Expr
type1, type2, type3, type4, type5, type6, type7, type8 :: Type

ex1 = Number 9
type1 = TInt

ex2 = Boolean False
type2 = TBool

ex3 = Prim "not"
type3 =  TFun TBool TBool

ex4 = App (Prim "not") (Boolean True)
type4 = TBool

ex5 = App (Prim ">") (Number 0)
type5 = TFun TInt TBool

ex6 = App (App (Prim "+") (Boolean True)) (Number 5)
type6 = TErr

ex7 = Cond (Boolean True) (Boolean False) (Id "c")
type7 = TBool

ex8 = Cond (App (Prim "==") (Number 4)) (Id "b") (Id "c")
type8 = TErr

------------------------------------------------------
-- Unification test cases from Table 2...

u1a, u1b, u2a, u2b, u3a, u3b, u4a, u4b, u5a, u5b, u6a, u6b :: Type
sub1, sub2, sub3, sub4, sub5, sub6 :: Maybe Sub

u1a = TFun (TVar "a") TInt
u1b = TVar "b"
sub1 = Just [("b",TFun (TVar "a") TInt)]

u2a = TFun TBool TBool
u2b = TFun TBool TBool
sub2 = Just []

u3a = TFun (TVar "a") TInt
u3b = TFun TBool TInt
sub3 = Just [("a",TBool)]

u4a = TBool
u4b = TFun TInt TBool
sub4 = Nothing

u5a = TFun (TVar "a") TInt
u5b = TFun TBool (TVar "b")
sub5 = Just [("b",TInt),("a",TBool)]

u6a = TFun (TVar "a") (TVar "a")
u6b = TVar "a"
sub6 = Nothing

------------------------------------------------------
-- Polymorphic type inference test cases from Table 3...

ex9, ex10, ex11, ex12, ex13, ex14 :: Expr
type9, type10, type11, type12, type13, type14 :: Type

ex9 = Fun "x" (Boolean True)
type9 = TFun (TVar "a1") TBool

ex10 = Fun "x" (Id "x")
type10 = TFun (TVar "a1") (TVar "a1")

ex11 = Fun "x" (App (Prim "not") (Id "x"))
type11 = TFun TBool TBool

ex12 = Fun "x" (Fun "y" (App (Id "y") (Id "x")))
type12 = TFun (TVar "a1") (TFun (TFun (TVar "a1") (TVar "a3")) (TVar "a3"))

ex13 = Fun "x" (Fun "y" (App (App (Id "y") (Id "x")) (Number 7)))
type13 = TFun (TVar "a1") (TFun (TFun (TVar "a1") (TFun TInt (TVar "a3")))
              (TVar "a3"))

ex14 = Fun "x" (Fun "y" (App (Id "x") (Prim "+")))
type14 = TFun (TFun (TFun TInt (TFun TInt TInt)) (TVar "a3"))
              (TFun (TVar "a2") (TVar "a3"))


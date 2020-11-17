-- file Name: project3.hs
-- file Author: Marco Borth, 2894114
-- description: project3 file containing Functions and Elaboration
{-# LANGUAGE GADTs #-}

-- Imports for Monads

import Control.Monad

-- FAE AST and Type Definitions

data FAE where
  Num :: Int -> FAE
  Plus :: FAE -> FAE -> FAE
  Minus :: FAE -> FAE -> FAE
  Lambda :: String -> FAE -> FAE
  App :: FAE -> FAE -> FAE
  Id :: String -> FAE
  deriving (Show,Eq)

type Env = [(String,FAE)]

evalAE :: FAE -> Int
evalAE (Num n) =
  if n >= 0
    then n :: Int
    else error "ERROR: Only Natural Numbers are Allowed"

evalAE (Plus l r) =
  let x = evalAE(l)
      y = evalAE(r)
      in x + y

evalAE (Minus l r) =
  let x = evalAE(l)
      y = evalAE(r)
      in if x >= y
        then x - y
        else error "ERROR: Resulting Difference must be Natural"

subst::String -> FAE -> FAE -> FAE
subst x v (Num n) = Num (evalAE (Num n))
subst x v (Plus l r) = Num (evalAE (Plus l r)) -- Plus (subst x v l) (subst x v r)
subst x v (Minus l r) = Num(evalAE (Minus l r))
subst x v (Lambda i b) = Lambda i (subst x v b)
--  if i == "inc"
--    then Num (evalAE (Plus b (Num 1)))
--    else Lambda i (subst x v b)
subst x v (Id a) =
  if x == a
    then v
    else Id a

evalDynFAE :: Env -> FAE -> (Maybe FAE)
evalDynFAE e (Num n) = Just (Num n)
evalDynFAE e (Plus l r) = Just (Num (evalAE (Plus l r) ) )
evalDynFAE e (Minus l r) = Just (Num (evalAE (Minus l r) ) )
evalDynFAE e (Lambda i b) = Just (Lambda i b)
evalDynFAE e (App f a) = do {
  (Lambda i b) <- (evalDynFAE e f);
  let prime = Num (evalAE a)
      in evalDynFAE e (subst i prime b)
}
evalDynFAE e (Id i) = lookup i e
--  if i == "inc"
--    then return (Num 1)
--    else return i



data FAEValue where
  NumV :: Int -> FAEValue
  ClosureV :: String -> FAE -> Env' -> FAEValue
  deriving (Show,Eq)

type Env' = [(String,FAEValue)]

evalStatFAE :: Env' -> FAE -> (Maybe FAEValue)
evalStatFAE e (Num n) = Just (NumV (evalAE (Num n)))
evalStatFAE e (Plus l r)  = Just (NumV (evalAE (Plus l r) ) )
evalStatFAE e (Minus l r)  = Just (NumV (evalAE (Minus l r) ) )
evalStatFAE e (Lambda i b) = Just (ClosureV i (Lambda i b) e)
evalStatFAE e (App f a) = Just (ClosureV "x" (App f a) e)
--evalStatFAE e (App f a) = do {
--  (Lambda i b) <- (evalStatFAE e f);
--  let prime = Num (evalAE a)
--    in (ClosureV "x" (evalStatFAE e (subst i prime b)) e)
--}
evalStatFAE e (Id i) = Just (ClosureV i (Id i) e)



-- FBAE AST and Type Definitions

data FBAE where
  NumD :: Int -> FBAE
  PlusD :: FBAE -> FBAE -> FBAE
  MinusD :: FBAE -> FBAE -> FBAE
  LambdaD :: String -> FBAE -> FBAE
  AppD :: FBAE -> FBAE -> FBAE
  BindD :: String -> FBAE -> FBAE -> FBAE
  IdD :: String -> FBAE
  deriving (Show,Eq)

elabFBAE :: FBAE -> FAE
elabFBAE (NumD n) = Num n
elabFBAE (PlusD l r) = Plus (elabFBAE l) (elabFBAE r)
elabFBAE (MinusD l r) = Minus (elabFBAE l) (elabFBAE r)
elabFBAE (LambdaD s a) = Lambda s (elabFBAE a)
elabFBAE (AppD f a) = App (elabFBAE f) (elabFBAE a)
elabFBAE (BindD i v b) = App (Lambda i (elabFBAE v)) (elabFBAE b)
elabFBAE (IdD i) = Id i

evalFBAE :: Env' -> FBAE -> (Maybe FAEValue)
evalFBAE e x = evalStatFAE e (elabFBAE x)



-- FBAEC AST and Type Definitions

data FBAEC where
  NumE :: Int -> FBAEC
  PlusE :: FBAEC -> FBAEC -> FBAEC
  MinusE :: FBAEC -> FBAEC -> FBAEC
  TrueE :: FBAEC
  FalseE :: FBAEC
  AndE :: FBAEC -> FBAEC -> FBAEC
  OrE :: FBAEC -> FBAEC -> FBAEC
  NotE :: FBAEC -> FBAEC
  IfE :: FBAEC -> FBAEC -> FBAEC -> FBAEC
  LambdaE :: String -> FBAEC -> FBAEC
  AppE :: FBAEC -> FBAEC -> FBAEC
  BindE :: String -> FBAEC -> FBAEC -> FBAEC
  IdE :: String -> FBAEC
  deriving (Show,Eq)

elabFBAEC :: FBAEC -> FAE
elabFBAEC (NumE n) = Num n
elabFBAEC (PlusE l r) = Plus (elabFBAEC l) (elabFBAEC r)
elabFBAEC (MinusE l r) = Minus (elabFBAEC l) (elabFBAEC r)

elabFBAEC (TrueE) =
  let i = "bool"
      t = (Num 1)
      f = (Num 0)
   in App (App (Lambda i (Lambda i t)) f) t

elabFBAEC (FalseE) =
 let i = "bool"
     t = (Num 1)
     f = (Num 0)
  in App (App (Lambda i (Lambda i f)) t) t

elabFBAEC (AndE x y) =
 let i = "x"
     j = "y"
     t = (Num 1)
     f = (Num 0)
  in App (App (Lambda i (Lambda j (elabFBAEC x) )) (elabFBAEC y)) f

elabFBAEC (OrE x y) =
 let i = "x"
     j = "y"
     t = (Num 1)
     f = (Num 0)
  in App (App (Lambda i (Lambda j (elabFBAEC x) )) t) (elabFBAEC y)

elabFBAEC (NotE x) =
 let i = "x"
     f = (Num 0)
  in App (Lambda i (elabFBAEC x) ) f

elabFBAEC (IfE c t e) =
  if elabFBAEC c == elabFBAEC (TrueE)-- if c == TrueE
    then elabFBAEC t
    else elabFBAEC e

elabFBAEC (LambdaE s a) = Lambda s (elabFBAEC a)
elabFBAEC (AppE f a) = App (elabFBAEC f) (elabFBAEC a)
elabFBAEC (BindE i v b) = App (Lambda i (elabFBAEC v)) (elabFBAEC b)
elabFBAEC (IdE i) = Id i

evalFBAEC :: Env' -> FBAEC -> Maybe FAEValue
evalFBAEC e x = evalStatFAE e (elabFBAEC x)
  -- let env = [("x",evalStatFAE env (elabFBAEC x))]
    -- in evalStatFAE env (elabFBAEC x)

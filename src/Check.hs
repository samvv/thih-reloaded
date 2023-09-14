module Check (
  Type(..),
  Kind(..),
  kStar,
  tUnit,
  tChar,
  tInt,
  tInteger,
  tFloat,
  tDouble,
  tList,
  tArrow,
  tTuple2,
  fn,
  list,
) where

import Control.Monad.Except
import Data.List (intersect, union, nub)
import qualified Data.Map as Map
import Control.Monad.State.Strict

type Id = String

data Kind
  = KCon Id | KFun Kind Kind
  deriving Eq

kStar :: Kind
kStar = KCon "*"

data Tyvar = Tyvar Id Kind
  deriving Eq

data Tycon = Tycon Id Kind
  deriving Eq

data Type
  = TVar Tyvar
  | TCon Tycon
  | TApp Type Type
  | Ten Int
  deriving Eq

tUnit, tChar, tInt, tInteger, tFloat, tDouble, tList, tArrow, tTuple2 :: Type

tUnit = TCon (Tycon "()" kStar)
tChar = TCon (Tycon "Char" kStar)
tInt = TCon (Tycon "Int" kStar)
tInteger = TCon (Tycon "Integer" kStar)
tFloat = TCon (Tycon "Float" kStar)
tDouble = TCon (Tycon "Double" kStar)

tList = TCon (Tycon "[]" (KFun kStar kStar))
tArrow = TCon (Tycon "(->)" (KFun kStar (KFun kStar kStar)))
tTuple2 = TCon (Tycon "(,)" (KFun kStar (KFun kStar kStar)))

infixr 4 `fn`
fn :: Type -> Type -> Type
a `fn` b = TApp (TApp tArrow a) b

list :: Type -> Type
list = TApp tList

class HasKind t where
  kind :: t -> Kind

instance HasKind Tyvar where
  kind (Tyvar v k) = k

instance HasKind Tycon where
  kind (Tycon v k) = k

instance HasKind Type where
  kind (TCon tc) = kind tc
  kind (TVar tv) = kind tv
  kind (TApp t _) = case kind t of
    KFun _ k -> k

type Subst = [(Tyvar, Type)]

nullSubst :: Subst
nullSubst = []

(+->) :: Tyvar -> Type -> Subst
u +-> t = [(u, t)]

class Types t where
  apply :: Subst -> t -> t
  tv :: t -> [Tyvar]

instance Types Type where
  apply s (TVar u) = case lookup u s of
    Just t -> t
    Nothing -> TVar u
  apply s (TApp l r) = TApp (apply s l) (apply s r)
  apply _ t = t
  tv (TVar u) = [u]
  tv (TApp l r) = tv l `union` tv r
  tv _ = []

instance Types a => Types [a] where
  apply s = map (apply s)
  tv = nub . concatMap tv

infixr 4 @@
(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = [(u, apply s1 t) | (u, t) <- s2] <> s1

type Solve a = Except String a

merge :: Subst -> Subst -> Solve Subst
merge s1 s2
  = if agree then pure (s1 <> s2) else throwError "merge fails"
  where agree = all (\v -> apply s1 (TVar v) == apply s2 (TVar v))
                    (map fst s1 `intersect` map fst s2)

mgu :: Type -> Type -> Solve Subst
mgu (TApp l r) (TApp l' r')
  = do s1 <- mgu l l'
       s2 <- mgu r r'
       return $ s2 @@ s1
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu (TCon tc1) (TCon tc2)
  | tc1 == tc2 = pure nullSubst
mgu _ _ = throwError "types do not unify"

varBind :: Tyvar -> Type -> Solve Subst
varBind u t
  | t == TVar u = pure nullSubst
  | u `elem` tv t = throwError "occurs check fails"
  | kind u /= kind t = throwError "kinds do not match"
  | otherwise = pure $ u +-> t

match :: Type -> Type -> Solve Subst
match (TApp l r) (TApp l' r')
  = do sl <- match l l'
       sr <- match r r'
       merge sl sr
match (TVar u) t | kind u == kind t = pure $ u +-> t
match (TCon tc1) (TCon tc2) | tc1 == tc2 = pure nullSubst
match _ _ = throwError "types do not match"

data Qual t = [ Pred ] :=> t
  deriving Eq

data Pred
  = IsIn Id Type
  deriving Eq

instance Types t => Types (Qual t) where
  apply s (ps :=> t) = apply s ps  :=> apply s t
  tv (ps :=> t) = tv ps  `union` tv t

instance Types Pred where
 apply s (IsIn i t) = IsIn i (apply s t)
 tv (IsIn _ t) = tv t

mguPred :: Pred -> Pred -> Solve Subst
mguPred = lift' mgu

matchPred :: Pred -> Pred -> Solve Subst
matchPred = lift' match

lift' :: (Type -> Type -> Solve Subst) -> Pred -> Pred -> Solve Subst
lift' m (IsIn i t) (IsIn i' t')
  | i == i' = m t t'
  | otherwise = throwError "classes differ"

data Class 
  = Class {
    classDepends :: [Id],
    classInstances :: [Inst]
  }

type Inst = Qual Pred

data ClassEnv 
  = ClassEnv {
    classes :: Map.Map Id Class,
    defaults :: [Type]
  }

super :: ClassEnv -> Id -> [Id]
super ce i = maybe [] classDepends (Map.lookup i (classes ce))

insts :: ClassEnv -> Id -> [Inst]
insts ce i = maybe [] classInstances (Map.lookup i (classes ce))

insert :: ClassEnv -> Id -> Class -> ClassEnv
insert ce i c = ce { classes = Map.insert i c (classes ce) }

type ClassM a = State ClassEnv a

addClass :: Id -> [Id] -> ClassM ()
addClass i is
  = void $ modify (\ce -> insert ce i $ Class is [])

initClasses :: ClassM ()
initClasses
   = do -- Core classes
        addClass "Eq"  []
        addClass "Ord" ["Eq"]
        addClass "Show" []
        addClass "Read" []
        addClass "Bounded" []
        addClass "Enum" []
        addClass "Functor" []
        addClass "Monad" []
        -- Numeric classes
        addClass "Num" ["Eq", "Show"]
        addClass "Real" ["Num", "Ord"]
        addClass "Fractional" ["Num"]
        addClass "Integral" ["Real", "Enum"]
        addClass "RealFrac" ["Real", "Fractional"]
        addClass "Floating" ["Fractional"]
        addClass "RealFloat" ["RealFrac", "Floating"]

initEnv :: ClassEnv
initEnv = ClassEnv { classes = Map.empty, defaults = [ tInteger, tDouble ] }


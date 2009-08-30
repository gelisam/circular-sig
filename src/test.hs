{-# LANGUAGE UnicodeSyntax #-}
import Control.Monad.Error


infixl  6 :⋅:
infixr  6 :→:

data Name
  = Const String
  | Bound Int
  | Unquoted Int
  deriving (Show, Eq)

-- inferable term
data TermI
  = Ann TermC Type
  | Ind Int
  | Nam Name
  | TermI :⋅: TermC
  deriving (Show, Eq)

-- checkable term
data TermC
  = Inf TermI
  | Lam TermC
  deriving (Show, Eq)

data Type
  = TNam Name
  | Type :→: Type
  deriving (Show, Eq)

data Value
  = VLam (Value → Value)
  | VNeu Neutral

data Neutral
  = NVar Name
  | NApp Neutral Value

instance Show Value where
  showsPrec p (VLam _) = ('l':)
                       . ('a':)
                       . ('m':)
                       . ('(':)
                       . ('.':)
                       . ('.':)
                       . ('.':)
                       . (')':)
  showsPrec p (VNeu x) = showsPrec p x

instance Show Neutral where
  showsPrec p (NVar x) = showsPrec p x
  showsPrec p (NApp x y) = ('(':)
                         . showsPrec p x
                         . (',':)
                         . showsPrec p y
                         . (')':)

vvar ∷ Name → Value
vvar n = VNeu (NVar n)


-- substituting (Ind i) for (Nam n)
deBruijnC ∷ Int → Name → TermC → TermC
deBruijnI ∷ Int → Name → TermI → TermI
deBruijnC i n (Inf x)   = Inf $ deBruijnI i     n x
deBruijnC i n (Lam x)   = Lam $ deBruijnC (i+1) n x
deBruijnI i n (Ann x t) = Ann (deBruijnC i n x) t
deBruijnI i n (Ind x)   = Ind x
deBruijnI i n (Nam x) | n == x    = Ind i
deBruijnI i n (Nam x) | otherwise = Nam x
deBruijnI i n (x :⋅: y) = deBruijnI i n x :⋅: deBruijnC i n y

-- substituting (Nam n) for (Ind i)
nameC ∷ Name → Int → TermC → TermC
nameI ∷ Name → Int → TermI → TermI
nameC n i (Inf x)   = Inf $ nameI n i     x
nameC n i (Lam x)   = Lam $ nameC n (i+1) x
nameI n i (Ann x t) = Ann (nameC n i x) t
nameI n i (Ind x) | i == x    = Nam n
nameI n i (Ind x) | otherwise = Ind x
nameI n i (Nam x)   = Nam x
nameI n i (x :⋅: y) = nameI n i x :⋅: nameC n i y

lam ∷ String → TermC → TermC
lam s x = Lam $ deBruijnC 0 (Const s) x

varC ∷ String → TermC
varI ∷ String → TermI
varT ∷ String → Type
varC n = Inf $ varI n
varI n = Nam $ Const n
varT n = TNam $ Const n

kC ∷ TermC
kT ∷ Type
kI ∷ TermI
kA ∷ TermI
kC = lam "x" $ lam "y" $ varC "x"
kT = varT "a" :→: varT "b" :→: varT "a"
kI = Ann kC kT
kA = kI :⋅: varC "u" :⋅: varC "v"


evalC ∷ [Value] → TermC → Value
evalI ∷ [Value] → TermI → Value
evalC env (Inf x)   = evalI env x
evalC env (Lam x)   = VLam $ \v → evalC (v : env) x
evalI env (Ann x t) = evalC env x
evalI env (Ind x)   = env !! x
evalI env (Nam x)   = vvar x
evalI env (x :⋅: y) = vapp (evalI env x) (evalC env y)

vapp ∷ Value → Value → Value
vapp (VLam f) e = f e
vapp (VNeu f) e = VNeu (NApp f e)

data Kind
  = Star
  deriving (Show, Eq)

data Info
  = HasKind Kind
  | HasType Type
  deriving (Show, Eq)

type Context = [(Name, Info)]
type Result a = Either String a


chk_kind ∷ Context → Type → Kind → Result ()
chk_kind c (TNam x) Star = case lookup x c of
  Just (HasKind Star) → return ()
  Nothing             →
    throwError $ "unknown type identifier "
              ++ show x
chk_kind c (x :→: y) Star = do
  chk_kind c x Star
  chk_kind c y Star

chk_type ∷ Context → TermC → Type → Result ()
chk_type c (Inf x) t = do
  t' ← inf_type c x
  unless (t == t') $
    throwError $ "term "
              ++ show x
              ++ " has type "
              ++ show t'
              ++ ", which doesn't match annotation "
                               ++ show t
chk_type c (Lam x) (t1 :→: t2) = chk_type c' x' t2 where
  name = Bound $ length c
  info = HasType t1
  c' = (name, info) : c
  x' = nameC name 0 x
chk_type c (Lam x) (TNam t) =
  throwError $ "term "
            ++ show (Lam x)
            ++ " has an arrow type, not "
            ++ show t
chk_type c (Inf x) (t1 :→: t2) =
  throwError $ "term "
            ++ show x
            ++ " is supposed to have type "
            ++ show (t1 :→: t2)
            ++ " but it is not a lambda"

inf_type ∷ Context → TermI → Result Type
inf_type c (Ann x t) = do
  chk_kind c t Star
  chk_type c x t
  return t
inf_type c (Ind x)   =
  throwError $ "index "
            ++ show x
            ++ " unexpected"
inf_type c (Nam x)   = case lookup x c of
  Just (HasType t) → return t
  Nothing          →
    throwError $ "unknown identifier "
              ++ show x
inf_type c (x :⋅: y) = do
  t ← inf_type c x
  case t of
    t1 :→: t2 → do
      chk_type c y t1
      return t2
    t'        →
      throwError $ "non-function term "
                ++ show x
                ++ " of type "
                ++ show t'
                ++ " applied to an argument"

quote  ∷       Value → TermC
quoteV ∷ Int → Value → TermC
quoteN ∷ Int → Neutral → TermI
quote v = quoteV 0 v
quoteV i (VLam f)   = Lam $ quoteV (i+1) $ f $ vvar $ Unquoted i
quoteV i (VNeu x)   = Inf $ quoteN i x
quoteN i (NVar x)   = requote i x
quoteN i (NApp x y) = quoteN i x :⋅: quoteV i y

requote ∷ Int → Name → TermI
requote i (Unquoted k) = Ind $ i - k - 1
requote i x            = Nam x


main = do
  putStrLn $ show kC
  putStrLn $ show $ evalC [] $ Inf kA
  putStrLn $ show $ chk_kind [(Const "a", HasKind Star)
                             ,(Const "b", HasKind Star)]
                             kT Star
  putStrLn $ show $ chk_type [(Const "a", HasKind Star)
                             ,(Const "b", HasKind Star)
                             ,(Const "u", HasType $ varT "a")
                             ,(Const "v", HasType $ varT "b")]
                             (Inf kA) (varT "a")
  putStrLn $ show $ inf_type [(Const "a", HasKind Star)
                             ,(Const "b", HasKind Star)
                             ,(Const "u", HasType $ varT "a")
                             ,(Const "v", HasType $ varT "b")]
                             kA
  putStrLn $ show $ quote $ evalC [] $ Inf kA
  putStrLn $ show $ quote $ evalC [] kC
  putStrLn "typechecks."

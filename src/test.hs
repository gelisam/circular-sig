{-# LANGUAGE UnicodeSyntax #-}
import Prelude hiding (pi)
import Control.Monad.Error


infixl  6 :⋅:
infixr  6 →→

data Name
  = Const String
  | Bound Int
  | Unquoted Int
  deriving (Show, Eq)

-- inferable term
data TermI
  = Ann TermC TermC
  | Star
  | Pi TermC TermC
  | Ind Int
  | Nam Name
  | TermI :⋅: TermC
  deriving (Show, Eq)

-- checkable term
data TermC
  = Inf TermI
  | Lam TermC
  deriving (Show, Eq)

type Type = Value

star ∷ TermC
star = Inf Star

(→→) ∷ TermC → TermC → TermC
t1 →→ t2 = Inf $ Pi t1 (bumpC 0 t2)

lam ∷ String → TermC → TermC
lam s x = Lam $ deBruijnC 0 (Const s) x

pi ∷ String → TermC → TermC → TermC
pi s x y = Inf $ Pi x $ deBruijnC 0 (Const s) y

data Value
  = VLam (Value → Value)
  | VStar
  | VPi Value (Value → Value)
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

(→→→) ∷ Value → Value → Value
x →→→ y = VPi x $ \_ → y


-- incrementing free indices i and above
bumpC ∷ Int → TermC → TermC
bumpI ∷ Int → TermI → TermI
bumpC i (Inf x)   = Inf $ bumpI i     x
bumpC i (Lam x)   = Lam $ bumpC (i+1) x
bumpI i (Ann x t) = Ann (bumpC i x) t
bumpI i Star      = Star
bumpI i (Pi x y)  = Pi (bumpC i x) (bumpC i y)
bumpI i (Ind x) | x >= i    = Ind (x + 1)
bumpI i (Ind x) | otherwise = Ind x
bumpI i (Nam x)   = Nam x
bumpI i (x :⋅: y) = bumpI i x :⋅: bumpC i y

-- substituting (Ind i) for (Nam n)
deBruijnC ∷ Int → Name → TermC → TermC
deBruijnI ∷ Int → Name → TermI → TermI
deBruijnC i n (Inf x)   = Inf $ deBruijnI i     n x
deBruijnC i n (Lam x)   = Lam $ deBruijnC (i+1) n x
deBruijnI i n (Ann x t) = Ann (deBruijnC i n x) t
deBruijnI i n Star      = Star
deBruijnI i n (Pi x y)  = Pi (deBruijnC i n x) (deBruijnC (i+1) n y)
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
nameI n i Star      = Star
nameI n i (Pi x y)  = Pi (nameC n i x) (nameC n (i+1) y)
nameI n i (Ind x) | i == x    = Nam n
nameI n i (Ind x) | otherwise = Ind x
nameI n i (Nam x)   = Nam x
nameI n i (x :⋅: y) = nameI n i x :⋅: nameC n i y

varC ∷ String → TermC
varI ∷ String → TermI
varV ∷ String → Value
varN ∷ String → Neutral
varC n = Inf $ varI n
varI n = Nam $ Const n
varV n = VNeu $ varN n
varN n = NVar $ Const n


evalC ∷ [Value] → TermC → Value
evalI ∷ [Value] → TermI → Value
evalC env (Inf x)   = evalI env x
evalC env (Lam x)   = VLam $ \v → evalC (v : env) x
evalI env (Ann x t) = evalC env x
evalI env Star      = VStar
evalI env (Pi x y)  = VPi (evalC env x) $ \v → evalC (v : env) y
evalI env (Ind x)   = env !! x
evalI env (Nam x)   = vvar x
evalI env (x :⋅: y) = vapp (evalI env x) (evalC env y)

vapp ∷ Value → Value → Value
vapp (VLam f) e = f e
vapp (VNeu f) e = VNeu (NApp f e)

type Context = [(Name, Type)]
type Result a = Either String a


chk_type ∷ Context → TermC → Type → Result ()
chk_type c (Inf x) t = do
  t' ← inf_type c x
  let qt  = quote t
  let qt' = quote t'
  unless (qt == qt') $
    throwError $ "term "
              ++ show x
              ++ " has type "
              ++ show qt'
              ++ ", which doesn't match annotation "
              ++ show qt
chk_type c (Lam x) (VPi t f) = do
  let name = Bound $ length c
  let c'   = (name, t) : c
  let x'   = nameC name 0 x
  let t2'  = f $ vvar name
  chk_type c' x' t2'
chk_type c (Lam x) VStar =
  throwError $ "term "
            ++ show (Lam x)
            ++ " has a pi type, not "
            ++ show (quote VStar)
chk_type c (Lam x) (VLam t) =
  throwError $ "term "
            ++ show (Lam x)
            ++ " has a pi type, not "
            ++ show (quote (VLam t))
chk_type c (Lam x) (VNeu t) =
  throwError $ "term "
            ++ show (Lam x)
            ++ " has a pi type, not "
            ++ show (quote (VNeu t))

inf_type ∷ Context → TermI → Result Type
inf_type c (Ann x t) = do
  chk_type c t VStar
  let v = evalC [] t
  chk_type c x v
  return v
inf_type c Star      = return VStar
inf_type c (Pi x y)  = do
  chk_type c x VStar
  let v    = evalC [] x
  let name = Bound $ length c
  let c'   = (name, v) : c
  let y'   = nameC name 0 y
  chk_type c' y' VStar
  return VStar
inf_type c (Ind x)   =
  throwError $ "index "
            ++ show x
            ++ " unexpected"
inf_type c (Nam x)   = case lookup x c of
  Just t  → return t
  Nothing →
    throwError $ "unknown identifier "
              ++ show x
inf_type c (x :⋅: y) = do
  t ← inf_type c x
  case t of
    VPi v f → do
      chk_type c y v
      return $ f $ evalC [] y
    t'      →
      throwError $ "non-function term "
                ++ show x
                ++ " of type "
                ++ show t'
                ++ " applied to an argument"


quote  ∷       Value → TermC
quoteV ∷ Int → Value → TermC
quoteN ∷ Int → Neutral → TermI
quote v = quoteV 0 v
quoteV i (VLam f)   = Lam f' where
  i' = vvar $ Unquoted i
  f' = quoteV (i+1) $ f i'
quoteV i VStar      = star
quoteV i (VPi x f)  = Inf $ Pi x' f' where
  i' = vvar $ Unquoted i
  x' = quoteV i x
  f' = quoteV (i+1) $ f i'
quoteV i (VNeu x)   = Inf $ quoteN i x
quoteN i (NVar x)   = requote i x
quoteN i (NApp x y) = quoteN i x :⋅: quoteV i y

requote ∷ Int → Name → TermI
requote i (Unquoted k) = Ind $ i - k - 1
requote i x            = Nam x


iC = lam "x" $ varC "x"
iT = varC "a" →→ varC "a"
iI = Ann iC iT
iA = iI :⋅: varC "y"
iK = [(Const "a", VStar)]
iKT = iK
   ++ [(Const "y", varV "a")]

kC = lam "x" $ lam "y" $ varC "x"
kT = varC "a" →→ varC "b" →→ varC "a"
kI = Ann kC kT
kA = kI :⋅: varC "u" :⋅: varC "v"
kK = [(Const "a", VStar)
     ,(Const "b", VStar)]
kKT = kK
   ++ [(Const "u", varV "a")
      ,(Const "v", varV "b")]

iiC = lam "a" $ lam "x" $ varC "x"
iiT = pi "a" star $ varC "a" →→ varC "a"
iiI = Ann iiC iiT
iiA = iiI :⋅: varC "Nat" :⋅: varC "zero"
iiK = [(Const "Nat", VStar)]
iiKT = iiK
    ++ [(Const "zero", varV "Nat")]

kkC = lam "a" $ lam "b" $ lam "x" $ lam "y" $ varC "x"
kkT = pi "a" star $ pi "b" star $ varC "a" →→ varC "b" →→ varC "a"
kkI = Ann kkC kkT
kkA = kkI :⋅: varC "Nat"  :⋅: varC "Bool"
          :⋅: varC "zero" :⋅: varC "false"
kkK = [(Const "Nat",  VStar)
      ,(Const "Bool", VStar)]
kkKT = kkK
   ++ [(Const "zero",  varV "Nat")
      ,(Const "false", varV "Bool")]


main = do
  putStrLn $ show iC
  putStrLn $ show kC
  putStrLn $ show iiC
  putStrLn $ show kkC
  putStrLn $ show $ evalC [] $ Inf iA
  putStrLn $ show $ evalC [] $ Inf kA
  putStrLn $ show $ evalC [] $ Inf iiA
  putStrLn $ show $ evalC [] $ Inf kkA
  putStrLn $ show $ chk_type iK  iT  VStar
  putStrLn $ show $ chk_type kK  kT  VStar
  putStrLn $ show $ chk_type iiK iiT VStar
  putStrLn $ show $ chk_type kkK kkT VStar
  putStrLn $ show $ chk_type iKT  (Inf iA)  (varV "a")
  putStrLn $ show $ chk_type kKT  (Inf kA)  (varV "a")
  putStrLn $ show $ chk_type iiKT (Inf iiA) (varV "Nat")
  putStrLn $ show $ chk_type kkKT (Inf kkA) (varV "Nat")
  putStrLn $ show $ inf_type iKT  iA
  putStrLn $ show $ inf_type kKT  kA
  putStrLn $ show $ inf_type iiKT iiA
  putStrLn $ show $ inf_type kkKT kkA
  putStrLn $ show $ quote $ evalC [] $ Inf iA
  putStrLn $ show $ quote $ evalC [] $ Inf kA
  putStrLn $ show $ quote $ evalC [] $ Inf iiA
  putStrLn $ show $ quote $ evalC [] $ Inf kkA
  putStrLn $ show $ quote $ evalC [] iC
  putStrLn $ show $ quote $ evalC [] kC
  putStrLn $ show $ quote $ evalC [] iiC
  putStrLn $ show $ quote $ evalC [] kkC
  putStrLn "typechecks."

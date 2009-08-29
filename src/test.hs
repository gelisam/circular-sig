{-# LANGUAGE UnicodeSyntax #-}

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


-- substituting i for the name (const s)
deBruijnC ∷ Int → String → TermC → TermC
deBruijnI ∷ Int → String → TermI → TermI
deBruijnC i s (Inf x)   = Inf $ deBruijnI i     s x
deBruijnC i s (Lam x)   = Lam $ deBruijnC (i+1) s x
deBruijnI i s (Ann x t) = Ann (deBruijnC i s x) t
deBruijnI i s (Ind x)   = Ind x
deBruijnI i s (Nam (Const x)) | s == x
                        = Ind i
deBruijnI i s (Nam x)   = Nam x
deBruijnI i s (x :⋅: y) = deBruijnI i s x :⋅: deBruijnC i s y

lam ∷ String → TermC → TermC
lam s x = Lam $ deBruijnC 0 s x

varC ∷ String → TermC
varI ∷ String → TermI
varT ∷ String → Type
varC n = Inf $ varI n
varI n = Nam $ Const n
varT n = TNam $ Const n

kC ∷ TermC
kI ∷ TermI
kC = lam "x" $ lam "y" $ varC "x"
kI = Ann kC $ varT "a" :→: varT "b"


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


main = do
  putStrLn $ show kC
  putStrLn $ show $ evalC [] $ Inf $
    kI :⋅: varC "u" :⋅: varC "v"
  putStrLn "typechecks."

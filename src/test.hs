{-# LANGUAGE UnicodeSyntax #-}

data Name
  = Const String
  | Bound Int
  | Unquoted Int
  deriving (Show, Eq)

data Inferable_Term
  = Ann Checkable_Term Type
  | Ind Int
  | Nam Name
  | Inferable_Term :⋅: Checkable_Term
  deriving (Show, Eq)

data Checkable_Term
  = Inf Inferable_Term
  | Lam Checkable_Term
  deriving (Show, Eq)

data Type
  = TPar Name
  | Type :→: Type
  deriving (Show, Eq)

data Value
  = VLam (Value → Value)
  | VNeu Neutral

data Neutral
  = NVar Name
  | NApp Neutral Value

vvar ∷ Name → Value
vvar n = VNeu (NVar n)


-- substituting i for the name (const s)
deBruijnC ∷ Int → String → Checkable_Term → Checkable_Term
deBruijnI ∷ Int → String → Inferable_Term → Inferable_Term
deBruijnC i s (Inf x)   = Inf $ deBruijnI i     s x
deBruijnC i s (Lam x)   = Lam $ deBruijnC (i+1) s x
deBruijnI i s (Ann x t) = Ann (deBruijnC i s x) t
deBruijnI i s (Ind x)   = Ind x
deBruijnI i s (Nam (Const x)) | s == x
                        = Ind i
deBruijnI i s (Nam x)   = Nam x
deBruijnI i s (x :⋅: y) = deBruijnI i s x :⋅: deBruijnC i s y

lam ∷ String → Checkable_Term → Checkable_Term
lam s x = Lam $ deBruijnC 0 s x

varC ∷ String → Checkable_Term
varI ∷ String → Inferable_Term
varC n = Inf $ varI n
varI n = Nam $ Const n

k ∷ Checkable_Term
k = lam "x" $ lam "y" $ varC "x"

main = do
  putStrLn $ show k
  putStrLn "typechecks."

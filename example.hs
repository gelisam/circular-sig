{-# OPTIONS_GHC -fglasgow-exts #-}

{- Gamma |- f : a -> b   Gamma |- t : a
 - ------------------------------------
 - Gamma |- f t : b
 - 
 - fmap_b (g t) = (fmap_(a->b) g) (fmap_a t)
 - fmap f (g t) = f (g t)
 - as desired... if (a) is interpreted as a fixed type distinct from b,
 - not as a schematic variable, even though (a) _is_ a schematic variable!!
 - 
 - what if (a) wasn't a fixed type distinct from b?
 - 
 - Gamma |- c : (int -> a) -> a   Gamma |- s : int -> a   Gamma |- i : int
 - ------------------------------------
 - Gamma |- c s : a
 - 
 - fmap_b (c s) = c' s' where
 -   c' = fmap_((int->a)->a) c
 -   s' = fmap_(int->a) s
 - fmap_b (c s) = c' s' where
 -   c' s' : (int -> b) -> b = (f . c) (f' . s')
 -   s' = f . s
 - fmap_b (c s) = f (c (f' . f . s))
 -              = f (c s)
 - as desired... if (f) and (f') are inverses.
 - but shouldn't this condition impose (f invertible) on fmap's argument?
 - 
 - ok, but if we _do_ impose (f . f' = id), can we make the argument that
 - (fmap (f x) = f (f x)) work in general?
 - 
 - fmap_b (g t) = (fmap_(a->b) g) (fmap_a t)
 -              = (f_b . g . f_a') (f_a t)
 -              = (f_b . g . f_a' . f_a) t
 -              = f_b (g t)
 - oh yeah, we can!
 -}

data Endo a = Endo (a -> a)

class Combined_Functor m where
  ffmap :: (a -> b) -> (b -> a) -> m a -> m b

instance Combined_Functor Endo where
  ffmap f f' (Endo g) = Endo (f . g . f')


{- Gamma, x : a |- f : b
 - -------------------------------
 - Gamma |- \x:a.b : a -> b
 - 
 - fmap_(a->b) b = b' where
 -   b' x' = fmap_b (b x)
 -   x = fmap'_a x'
 - fmap_(a->b) b = b' where
 -   b' x' = f_b (b (f'_a x'))
 - fmap_(a->b) b = f_b . b . f'_a
 -}

data Hom a b = Hom (a -> b)

class Combined_BiFunctor m where
  ffmap2 :: (x -> u) -> (u -> x) -> (y -> v) -> (v -> y) -> m x y -> m u v

instance Combined_BiFunctor Hom where
  ffmap2 f f' g g' (Hom h) = Hom (g . h . f')

{- Gamma |- b : t
 - -------------------------------
 - Gamma |- /a.b : forall a. t
 - 
 -}



{- Gamma |- f : e -> b   Gamma |- t : e
 - -------------------------------
 - Gamma |- Apply f t : exists a. (a -> b) X a
 - 
 -
 - fmap_b (g t) = (fmap_(e->b) g) (fmap_e t)
 -}

{- Gamma |- g : a -> b   Gamma |- g' : b -> a
 - ------------------------------------------
 - Gamma |- ffmap g g' : F a -> F b
 - 
 - ffmap_(F a -> F b) f f' (ffmap_F g g') = ffmap g2 g'2
 -   g2 = ffmap_(a -> b) g
 -   g'2 = ffmap_(b -> a) g'
 - ffmap f f' (ffmap g g') = ffmap (f_b . g . f'_a) (f_a . g' . f'_b)
 -   f_b . g . f'_a . f_a . g' . f'_b =
 -   f_b . g        .       g' . f'_b =
 -   f_b            .            f'_b = id
 -   f_a . g' . f'_b . f_b . g . f'_a =
 -   f_a . g'        .       g . f'_a =
 -   f_a             .           f'_a = id
 - ffmap f f' (ffmap g g') = ffmap (f_b . g . f'_a) (f_a . g' . f'_b)
 - true for any superscript, including b:
 - ffmap f f' (ffmap g g') = ffmap (f . g) (g' . f')
 -}




main = putStrLn "typechecks."

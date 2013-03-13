circular-sig
============

A normal application of dependent types would be to index the type Vector with values of type Nat, allowing us to keep track of the vector's length at the type level.

    nat :: type
    zero :: nat
    succ :: nat -> nat
    
    vector :: (A :: type) -> nat -> type
    nil :: vector A zero
    cons :: A -> vector A N -> vector A (succ N)
    
    -- for example, singleton creates a vector of length 1
    singleton :: A -> vector A (succ zero)
    singleton x = cons x nil


A simple variant is the type Vector+ of non-empty Vectors:

    nat+ :: type
    one :: nat+
    succ :: nat+ -> nat+
    
    vector+ :: (A :: type) -> nat -> type
    singleton :: vector A one
    cons :: A -> vector A N -> vector A (succ N)


At [CADE 2009](http://complogic.cs.mcgill.ca/cade22/), [Jason C. Reed](http://jcreed.livejournal.com/) and I discussed datatypes indexed by values of this same datatype. This is a very unusual form of recursion.

One example where this would be useful is the Matrix datatype. Just like we indexed the Vector type with its length, we would like to index Matrix with the sizes of its various dimentions. For a D-dimensional matrix, this list of size could easily be represented using a Vector of length D. But if we define a List to be a one-dimensional Matrix, we have a circular dependency!

    nat+ :: type
    one :: nat+
    succ :: nat+ -> nat+
    
    
    matrix :: (A :: type) -> (D :: nat+) -> vector nat+ D -> type
    
    -- a matrix of dimension one, whose length
    -- along that dimension is also one
    atom :: A -> matrix A one (singleton one)
    
    -- lengthening a matrix of dimension one
    cons1 :: matrix A one (singleton one)
          -> matrix A one (singleton L)
          -> matrix A one (singleton (succ L))
    
    -- adding a row to an existing 2D matrix,
    -- or a plane to an existing 3D matrix, etc.
    cons+ :: (D :: nat+)
          -> (LS :: vector nat+ D)
          -> matrix A (succ D) (cons one      LS)
          -> matrix A (succ D) (cons L        LS)
          -> matrix A (succ D) (cons (succ L) LS)
    
    -- bumping a 1D matrix up to a 2D matrix of height 1,
    -- or a 2D matrix up to a 3D matrix of depth 1, etc.
    bump :: matrix A D LS
         -> matrix A (succ D) (cons one LS)
    
    -- and now for the big reveal: vector was a matrix all along!
    vector :: (A :: type) -> (L : nat+) -> type
    vector A L = matrix A one (singleton L)
    
    singleton :: A -> vector A one
    singleton x = atom x
    
    cons :: A -> vector A L -> vector A (succ L)
    cons x xs = cons1 (atom x) xs


This repository contains Haskell code to type-check mutually-recursive signatures such as the above.

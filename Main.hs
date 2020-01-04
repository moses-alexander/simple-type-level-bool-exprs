{-# LANGUAGE AllowAmbiguousTypes#-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Data.Typeable
import GHC.TypeLits


main :: IO ()
main = do
    print "..."
    let a = Proxy :: Proxy (Rdc (Neg T))
    let b = unproxy a
    -- let c = proxy $ RNN (NN (NT Tt))
    -- let d = unproxy c
    print (b :: F)
    {- 
    won't compile, GHC will complain that the expected type 'F'
    doesn't match the type 'T' i'm asking for.
    print (b :: T)
    -}
    -- print (d :: T)


data T = Tt deriving (Show, Typeable)
data F = Ff deriving (Show, Typeable)
data U = Uu deriving (Show, Typeable)

data Expr a where
    ET :: T       -> Expr T
    EF :: F       -> Expr F
    EN :: Neg a   -> Expr (Neg a)
    EA :: And a b -> Expr (And a b)
    EO :: Or a b  -> Expr (Or a b)
    ER :: Rdcd a  -> Expr (Rdcd a)

data Neg a where
    NT :: T     -> Neg T
    NF :: F     -> Neg F
    NN :: Neg a -> Neg (Neg a)

data And a b where
    ATT :: T -> T -> And T T
    ATF :: T -> F -> And T F
    AFT :: F -> T -> And F T
    AFF :: F -> F -> And F F

data Or a b where
    OTT :: T -> T -> Or T T
    OTF :: T -> F -> Or T F
    OFT :: F -> T -> Or F T
    OFF :: F -> F -> Or F F

data If a b where
    ITT :: T -> T -> If T T
    ITF :: T -> F -> If T F
    IFT :: F -> T -> If F T
    IFF :: F -> F -> If F F


data Iff a b where
    IFFTT :: T -> T -> Iff T T
    IFFTF :: T -> F -> Iff T F
    IFFFT :: F -> T -> Iff F T
    IFFFF :: F -> F -> Iff F F

data Rdcd a where
    RT :: T -> Rdcd T
    RF :: F -> Rdcd F
    RU :: a -> Rdcd a


type family Rdc e :: * where
    Rdc T                       = Rdcd T
    Rdc F                       = Rdcd F
    Rdc (Neg T)                 = Rdcd F
    Rdc (Neg F)                 = Rdcd T
    Rdc (Neg U)                 = Rdcd U
    Rdc (Neg (Rdcd x))          = Rdc (Neg x)
    Rdc (Neg x)                 = Rdc (Neg (Rdc x))
    Rdc (And (Rdcd x) (Rdcd y)) = Rdc (And x y)
    Rdc (And (Rdcd x) y)        = Rdc (And x (Rdc y))
    Rdc (And x (Rdcd y))        = Rdc (And (Rdc x) y)
    Rdc (And T T)               = Rdcd T
    Rdc (And F _)               = Rdcd F
    Rdc (And _ F)               = Rdcd F
    Rdc (And _ U)               = Rdcd U
    Rdc (And U _)               = Rdcd U
    Rdc (And x y)               = Rdc (And (Rdc x) (Rdc y))
    Rdc (Or (Rdcd x) (Rdcd y))  = Rdc (Or x y)
    Rdc (Or (Rdcd x) y)         = Rdc (Or x (Rdc y))
    Rdc (Or x (Rdcd y))         = Rdc (Or (Rdc x) y)
    Rdc (Or F F)                = Rdcd F
    Rdc (Or T _)                = Rdcd T
    Rdc (Or _ T)                = Rdcd T
    Rdc (Or _ U)                = Rdcd U
    Rdc (Or U _)                = Rdcd U
    Rdc (Or x y)                = Rdc (Or (Rdc x) (Rdc y))
    Rdc (If (Rdcd x) (Rdcd y))  = Rdc (If x y)
    Rdc (If (Rdcd x) y)         = Rdc (If x (Rdc y))
    Rdc (If x (Rdcd y))         = Rdc (If (Rdc x) y)
    Rdc (If F F)                = Rdcd T
    Rdc (If T F)                = Rdcd F
    Rdc (If T T)                = Rdcd T
    Rdc (If F T)                = Rdcd T
    Rdc (If _ U)                = Rdcd U
    Rdc (If U _)                = Rdcd U
    Rdc (If x y)                = Rdc (If (Rdc x) (Rdc y))
    Rdc (Iff (Rdcd x) (Rdcd y)) = Rdc (Iff x y)
    Rdc (Iff (Rdcd x) y)        = Rdc (Iff x (Rdc y))
    Rdc (Iff x (Rdcd y))        = Rdc (Iff (Rdc x) y)
    Rdc (Iff F F)               = Rdcd T
    Rdc (Iff T F)               = Rdcd F
    Rdc (Iff T T)               = Rdcd T
    Rdc (Iff F T)               = Rdcd F
    Rdc (Iff _ U)               = Rdcd U
    Rdc (Iff U _)               = Rdcd U
    Rdc (Iff x y)               = Rdc (Iff (Rdc x) (Rdc y))
    Rdc _                       = Rdcd U

instance Semigroup (Rdcd T) where
    RT Tt <> _ = RT Tt
    _ <> RT Tt = RT Tt
    _ <> _     = RU Tt

instance Semigroup (Rdcd F) where
    RF Ff <> _ = RF Ff
    _ <> RF Ff = RF Ff
    _ <> _     = RU Ff

proxy :: a -> Proxy a
proxy x = Proxy :: Proxy (x)

unwrap :: Rdcd a -> a
unwrap (RT Tt) = Tt
unwrap (RF Ff) = Ff

class Unproxy a where
    unproxy :: Proxy (Rdcd a) -> a

instance Unproxy T where
    unproxy x = Tt

instance Unproxy F where
    unproxy x = Ff


-- test0 = Proxy :: Proxy (Rdc (U))
-- test1 = Proxy :: Proxy (Rdc (And (Neg (Or F F)) (And T T)))
-- test2 = Proxy :: Proxy (Rdc (Neg (And T F)))
-- test3 = Proxy :: Proxy (Rdc (Neg (Neg (Neg (Neg (Neg T))))))
-- test4 = Proxy :: Proxy (Rdc (And T F))
-- test5 = Proxy :: Proxy (Rdc (And (And (And T T) (And F T)) (Neg F)))
-- test6 = Proxy :: Proxy (Rdc (Neg (And (Neg (Or F (Neg (Or F F)))) T)))
-- test7 = Proxy :: Proxy (Rdc (Neg (Or (Neg (Or F (Neg (Or F F)))) (Neg (If T (Iff F (Or T (And F F))))))))

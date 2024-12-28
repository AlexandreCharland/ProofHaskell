{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

data Nat = Z | S Nat
data a :~: b where
  Refl :: a :~: a

type family a + b where
  a + Z   = a
  a + S b = S (a + b)

type family a . b where -- Il ne me laissait pas choisir le symbole *
  a . Z   = Z
  a . S b = a + (a . b)

data SNat :: Nat -> * where
  SZ :: SNat Z
  SS :: SNat a -> SNat (S a)

gcastWith :: (a :~: b) -> (a ~ b => r) -> r
gcastWith Refl x = x

(==>) :: a :~: b -> b :~: c -> a :~: c
Refl ==> Refl = Refl

(!+) :: SNat n -> SNat m -> SNat (n + m)
n !+ SZ     = n
n !+ (SS m) = SS (n !+ m)

(!.) :: SNat n -> SNat m -> SNat (n . m)
n !. SZ     = SZ
n !. (SS m) = n !+ (n !. m)

-- Lemmas

addZero :: SNat a -> (a + Z) :~: a
addZero _ = Refl

addSucc :: SNat a -> SNat b -> (a + S b) :~: S (a + b)
addSucc _ _ = Refl

zeroAdd :: SNat a -> (Z + a) :~: a
zeroAdd SZ = Refl -- Cas de base
zeroAdd (SS a) = gcastWith (zeroAdd a) Refl -- Pas d'induction

addAssoc :: SNat a -> SNat b -> SNat c -> ((a + b) + c) :~: (a + (b + c))
addAssoc a b SZ = -- Il faut mq ((a + b) + 0) = (a + (b + 0))
  let
    step1 :: SNat x -> SNat y -> ((x + y) + Z) :~: (x + y) -- ((a + b) + 0) = (a + b)
    step1 x y = gcastWith (addZero (x !+ y)) Refl

    step2 :: SNat x -> SNat y -> (x + y) :~: (x + (y + Z)) -- (a + b) = (a + (b + 0))
    step2 x y = gcastWith (addZero y) Refl
  in step1 a b ==> step2 a b
addAssoc a b (SS c) = -- Il faut mq ((a + b) + (S c)) = (a + (b + (S c))) sachant que ((a + b) + c) = (a + (b + c))
  let
    step1 :: SNat x -> SNat y -> SNat (S z) -> ((x + y) + S z) :~: S ((x + y) + z) -- ((a + b) + (S c)) = (S (a + b) + c)
    step1 x y (SS z) = gcastWith (addSucc (a !+ b) (SS z)) Refl

    step2 :: SNat x -> SNat y -> SNat z -> S ((x + y) + z) :~: S (x + (y + z)) -- (S (a + b) + c) = (S a + (b + c))
    step2 x y z = gcastWith (addAssoc x y z) Refl

    step3 :: SNat x -> SNat y -> SNat z -> S (x + (y + z)) :~: (x + S (y + z)) -- (S a + (b + c)) = (a + S (b + c))
    step3 x y z = gcastWith (addSucc x (y !+ z)) Refl

    step4 :: SNat x -> SNat y -> SNat z -> (x + S (y + z)) :~: (x + (y + S z)) -- (a + S (b + c)) = (a + (b + S c))
    step4 x y z = gcastWith (addSucc y z) Refl
  in step1 a b (SS c) ==> step2 a b c ==> step3 a b c ==> step4 a b c

succAdd :: SNat a -> SNat b -> (S a + b) :~: S (a + b)
succAdd a SZ = Refl
succAdd a (SS b) = -- Il faut mq (S a + S b) = S (a + S b) sachant que (S a + b) = S (a + b)
  let
    step1 :: SNat x -> SNat (S y) -> (S x + S y) :~: S (S x + y) -- (S a + S b) = S (S a + b)
    step1 x (SS y) = gcastWith (addSucc x y) Refl

    step2 :: SNat x -> SNat y -> S (S x + y) :~: S (S (x + y)) -- S (S a + b) = S S (a + b)
    step2 x y = gcastWith (succAdd x y) Refl

    step3 :: SNat x -> SNat y -> S (S (x + y)) :~: S (x + S y) -- S S (a + b) = S (a + S b)
    step3 x y = gcastWith (addSucc x y) Refl
  in step1 a (SS b) ==> step2 a b ==> step3 a b

addComm :: SNat a -> SNat b -> (a + b) :~: (b + a)
addComm a SZ =
  let
    step1 :: SNat x -> (x + Z) :~: x -- (x + 0) = x
    step1 x = gcastWith (addZero x) Refl

    step2 :: SNat x -> x :~: (Z + x) -- x = (0 + x)
    step2 x = gcastWith (zeroAdd x) Refl
  in step1 a ==> step2 a
addComm a (SS b) = -- Il faut mq (a + S b) = (S b + a) sachant que (a + b) = (b + a)
  let
    step1 :: SNat x -> SNat (S y) -> (x + S y) :~: S (x + y) -- (a + S b) = S (a + b)
    step1 x (SS y) = gcastWith (addSucc x y) Refl

    step2 :: SNat x -> SNat y -> S (x + y) :~: S (y + x) -- S (a + b) = S (b + a)
    step2 x y = gcastWith (addComm x y) Refl

    step3 :: SNat x -> SNat y -> S (y + x) :~: (S y + x) -- S (b + a) = (S b + a)
    step3 x y = gcastWith (succAdd y x) Refl
  in step1 a (SS b) ==> step2 a b ==> step3 a b

mulZero :: SNat a -> (a . Z) :~: Z
mulZero _ = Refl

mulSucc :: SNat a -> SNat b -> (a . S b) :~: (a + (a . b))
mulSucc _ _ = Refl

zeroMul :: SNat a -> (Z . a) :~: Z
zeroMul SZ = Refl
zeroMul (SS a) = gcastWith (zeroMul a) Refl

mulOne :: SNat a -> (a . S Z) :~: a
mulOne a =
  let
    step1 :: SNat x -> (x . S Z) :~: (x + (x . Z)) -- (x * 1) :~: (x + (x * 0))
    step1 x = gcastWith (mulSucc x SZ) Refl

    step2 :: SNat x -> (x + (x . Z)) :~: (x + Z) -- (x + (x * 0)) = (x + 0)
    step2 x = gcastWith (mulZero a) Refl

    step3 :: SNat x -> (x + Z) :~: x -- (x + 0) = x
    step3 x = gcastWith (addZero x) Refl
  in step1 a ==> step2 a ==> step3 a

oneMul :: SNat a -> (S Z . a) :~: a
oneMul SZ = gcastWith (mulZero SZ) Refl
oneMul (SS a) = -- Il faut mq (1 * S a) :~: S a sachant que (1 * a) :~: a
  let
    step1 :: SNat (S x) -> (S Z . S x) :~: (S Z + (S Z . x)) -- (1 * S x) = (1 + (1 * x))
    step1 x = gcastWith (mulSucc SZ x) Refl

    step2 :: SNat x -> (S Z + (S Z . x)) :~: (S Z + x) -- (1 + (1 + x)) = (1 + x)
    step2 x = gcastWith (oneMul x) Refl

    step3 :: SNat x -> (S Z + x) :~: S (Z + x) -- (1 + x) = S (0 + x)
    step3 x = gcastWith (succAdd SZ x) Refl

    step4 :: SNat x -> S (Z + x) :~: S x -- S (0+ x) = S x
    step4 x = gcastWith (zeroAdd x) Refl
  in step1 (SS a) ==> step2 a ==> step3 a ==> step4 a
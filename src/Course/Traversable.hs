{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}

module Course.Traversable where

import Course.Core
import Course.Functor
import Course.Applicative
import Course.List
import Course.ExactlyOne
import Course.Optional
import Course.Compose

-- | All instances of the `Traversable` type-class must satisfy three laws. These
-- laws are not checked by the compiler. These laws are given as:
--
-- * The law of naturality
--   `∀f g. f . traverse g ≅ traverse (f . g)`
--
-- * The law of identity
--   `∀x. traverse ExactlyOne x ≅ ExactlyOne x`
--
-- * The law of composition
--   `∀f g. traverse ((g <$>) . f) ≅ (traverse g <$>) . traverse f`
class Functor t => Traversable t where
  traverse ::
    Applicative f =>
    (a -> f b)
    -> t a
    -> f (t b)

instance Traversable List where
  traverse ::
    Applicative f =>
    (a -> f b)
    -> List a
    -> f (List b)
  -- {-# INLINE traverse #-}
  -- traverse f =
  --   foldRight (lift2 (:.) . f) (pure Nil)
  traverse _ Nil =
    pure Nil
  traverse g (h:.t) =
    let fb = g h
        flb = traverse g t
    in lift2 (flip (:.)) flb fb -- order matters ..

instance Traversable ExactlyOne where
  traverse ::
    Applicative f =>
    (a -> f b)
    -> ExactlyOne a
    -> f (ExactlyOne b)
  traverse f (ExactlyOne a) =
    ExactlyOne <$> f a

instance Traversable Optional where
  traverse ::
    Applicative f =>
    (a -> f b)
    -> Optional a
    -> f (Optional b)
  traverse f k = case k of
    Empty  -> pure Empty
    Full a -> Full <$> f a 
    

-- | Sequences a traversable value of structures to a structure of a traversable value.
--
-- >>> sequenceA (ExactlyOne 7 :. ExactlyOne 8 :. ExactlyOne 9 :. Nil)
-- ExactlyOne [7,8,9]
--
-- >>> sequenceA (Full (ExactlyOne 7))
-- ExactlyOne (Full 7)
--
-- >>> sequenceA (Full (*10)) 6
-- Full 60
sequenceA ::
  (Applicative f, Traversable t) =>
  t (f a)
  -> f (t a)
sequenceA =
  traverse id

instance (Traversable f, Traversable g) =>
  Traversable (Compose f g) where
-- Implement the traverse function for a Traversable instance for Compose
  traverse ::
    Applicative h =>
    (a -> h b)
    -> Compose f g a
    -> h (Compose f g b)
--  1.-      g a -> h g b
--   ga ≅ a = a  ->  h b
--  2.- f a -> h f a  ≅  f g a -> h f g a 
  traverse f (Compose fga) = 
    Compose <$> traverse (traverse f) fga


-- | The `Product` data type contains one value from each of the two type constructors.
data Product f g a =
  Product (f a) (g a) deriving (Show, Eq)

instance (Functor f, Functor g) =>
  Functor (Product f g) where
-- Implement the (<$>) function for a Functor instance for Product
  f <$> Product fa ga =
    Product (f <$> fa) (f <$> ga)
    

instance (Traversable f, Traversable g) =>
  Traversable (Product f g) where
-- Implement the traverse function for a Traversable instance for Product
  traverse ::
    Applicative h =>
    (a -> h b)
    -> Product f g a
    -> h (Product f g b)
  traverse f (Product fa ga)=
    lift2 Product (traverse f fa) (traverse f ga)
    

-- | The `Coproduct` data type contains one value from either of the two type constructors.
data Coproduct f g a =
  InL (f a)
  | InR (g a) deriving (Show, Eq)

instance (Functor f, Functor g) =>
  Functor (Coproduct f g) where
-- Implement the (<$>) function for a Functor instance for Coproduct
  f <$> coproduct = case coproduct of
    InL fa -> InL (f <$> fa)
    InR ga -> InR (f <$> ga)
   

instance (Traversable f, Traversable g) =>
  Traversable (Coproduct f g) where
-- Implement the traverse function for a Traversable instance for Coproduct
  traverse f coproduct = case coproduct of
    InL fa -> InL <$> traverse f fa
    InR ga -> InR <$> traverse f ga

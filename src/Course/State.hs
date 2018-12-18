{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TupleSections #-}

module Course.State where

import Course.Core
import qualified Prelude as P
import Course.Optional
import Course.List
import Course.Functor
import Course.Applicative
import Course.Monad
import qualified Data.Set as S
import qualified Data.Char as C 
-- $setup
-- >>> import Test.QuickCheck.Function
-- >>> import Data.List(nub)
-- >>> import Test.QuickCheck
-- >>> import qualified Prelude as P(fmap, fromInteger)
-- >>> import Course.Core
-- >>> import Course.List
-- >>> instance Arbitrary a => Arbitrary (List a) where arbitrary = P.fmap listh arbitrary

-- A `State` is a function from a state value `s` to (a produced value `a`, and a resulting state `s`).
newtype State s a =
  State {
    runState ::
      s
      -> (a, s)
  }

-- | Run the `State` seeded with `s` and retrieve the resulting state.
--
-- prop> \(Fun _ f) s -> exec (State f) s == snd (runState (State f) s)
exec ::
  State s a
  -> s
  -> s
exec =
  (snd .) . runState

-- | Run the `State` seeded with `s` and retrieve the resulting value.
--
-- prop> \(Fun _ f) s -> eval (State f) s == fst (runState (State f) s)
eval ::
  State s a
  -> s
  -> a
eval =
  (fst .) . runState
  

-- | A `State` where the state also distributes into the produced value.
--
-- >>> runState get 0
-- (0,0)
get ::
  State s s
get =
  State $ \s -> (s, s)

gets ::
  (s -> a)
  -> State s a
gets f = f <$> get 

-- | A `State` where the resulting state is seeded with the given value.
--
-- >>> runState (put 1) 0
-- ((),1)
put ::
  s
  -> State s ()
put s =
  State $ const ((), s)

modify ::
  (s -> s)
  -> State s ()
modify f =
  get >>= (put . f)

-- | Implement the `Functor` instance for `State s`.
--
-- >>> runState ((+1) <$> State (\s -> (9, s * 2))) 3
-- (10,6)
instance Functor (State s) where
  (<$>) ::
    (a -> b)
    -> State s a
    -> State s b
  (<$>) f (State sa) =
    State $ \s -> case sa s of
      (a, s1) -> (f a, s1)

-- | Implement the `Applicative` instance for `State s`.
--
-- >>> runState (pure 2) 0
-- (2,0)
--
-- >>> runState (pure (+1) <*> pure 0) 0
-- (1,0)
--
-- >>> import qualified Prelude as P
-- >>> runState (State (\s -> ((+3), s P.++ ["apple"])) <*> State (\s -> (7, s P.++ ["banana"]))) []
-- (10,["apple","banana"])
instance Applicative (State s) where
  pure ::
    a
    -> State s a
  pure a =
    State (a,)
  (<*>) ::
    State s (a -> b)
    -> State s a
    -> State s b 
  (<*>) (State sf) (State sa) =
    State $ \s -> case sf s of
      (f, s1) -> case sa s1 of
        (a, s2) -> (f a, s2)
    

-- | Implement the `Bind` instance for `State s`.
--
-- >>> runState ((const $ put 2) =<< put 1) 0
-- ((),2)
--
-- >>> let modify f = State (\s -> ((), f s)) in runState (modify (+1) >>= \() -> modify (*2)) 7
-- ((),16)
instance Monad (State s) where
  (=<<) ::
    (a -> State s b)
    -> State s a
    -> State s b
  (=<<) f (State sa) =
    State $ \s -> case sa s of
      (a, s1) -> (runState $ f a) s1
      
-- | Find the first element in a `List` that satisfies a given predicate.
-- It is possible that no element is found, hence an `Optional` result.
-- However, while performing the search, we sequence some `Monad` effect through.
--
-- Note the similarity of the type signature to List#find
-- where the effect appears in every return position:
--   find ::  (a ->   Bool) -> List a ->    Optional a
--   findM :: (a -> f Bool) -> List a -> f (Optional a)
--
-- >>> let p x = (\s -> (const $ pure (x == 'c')) =<< put (1+s)) =<< get in runState (findM p $ listh ['a'..'h']) 0
-- (Full 'c',3)
--
-- >>> let p x = (\s -> (const $ pure (x == 'i')) =<< put (1+s)) =<< get in runState (findM p $ listh ['a'..'h']) 0
-- (Empty,8)
findM ::
  Monad f =>
  (a -> f Bool)
  -> List a
  -> f (Optional a)
findM _ Nil = pure Empty
findM p (h :. t) = do
  q <- p h
  if q
    then pure $ Full h
  else findM p t

-- Find element and index, otherwise only the position State (Optional a, Integer)

findLetter ::
  Char ->
  (Optional Char, Integer)
findLetter c =
  let
    p :: Char -> State Integer Bool
    p x = do -- get >>= (\s -> put (1+s) >>= (const $ pure (x == c)))
        s1 <- get
        put (s1 + 1)
        pure $ x == c
  in runState (findM p $ listh ['a'..'h']) 0

-- | Find the first element in a `List` that repeats.
-- It is possible that no element repeats, hence an `Optional` result.
--
-- /Tip:/ Use `findM` and `State` with a @Data.Set#Set@.
--
-- prop> \xs -> case firstRepeat xs of Empty -> let xs' = hlist xs in nub xs' == xs'; Full x -> length (filter (== x) xs) > 1
-- prop> \xs -> case firstRepeat xs of Empty -> True; Full x -> let (l, (rx :. rs)) = span (/= x) xs in let (l2, r2) = span (/= x) rs in let l3 = hlist (l ++ (rx :. Nil) ++ l2) in nub l3 == l3


--seen <- gets (S.member a)
--if seen
--  then pure ()
--  else modify (S.insert a) *> pure seen
firstRepeat ::
  Ord a =>
  List a
  -> Optional a
firstRepeat l =
  let p a =  do
        seen <- gets (S.member a)
        unless seen (modify (S.insert a))
        pure seen
  in eval (findM p l) S.empty

-- | Remove all duplicate elements in a `List`.
-- /Tip:/ Use `filtering` and `State` with a @Data.Set#Set@.
--
-- prop> \xs -> firstRepeat (distinct xs) == Empty
--
-- prop> \xs -> distinct xs == distinct (flatMap (\x -> x :. x :. Nil) xs)
distinct ::
  Ord a =>
  List a
  -> List a
distinct l =
  let p a =  do
        seen <- gets (S.member a)
        if seen
          then pure False
          else modify (S.insert a) *> pure True 
  in eval (filtering p l) S.empty

-- | A happy number is a positive integer, where the sum of the square of its digits eventually reaches 1 after repetition.
-- In contrast, a sad number (not a happy number) is where the sum of the square of its digits never reaches 1
-- because it results in a recurring sequence.
--
-- /Tip:/ Use `firstRepeat` with `produce`.
--
-- /Tip:/ Use `join` to write a @square@ function.
--
-- /Tip:/ Use library functions: @Optional#contains@, @Data.Char#digitToInt@.
--
-- >>> isHappy 4
-- False
--
-- >>> isHappy 7
-- True
--
-- >>> isHappy 42
-- False
--
-- >>> isHappy 44
-- True
isHappy ::
  Integer
  -> Bool
isHappy =
  let loopF = toInteger . sum . map (join (*) . digitToInt) . listh . show
  in contains 1 . firstRepeat . produce loopF 

{-
Why does join (*) squares ?

join x = x >>= id:
  join (*) = (*) >>= id
(*) is a monad of (-> r) where >>= is defined as:
  f >>= k = \r -> k (f r) r
Then if the substitute:
  \r -> k (f r) r
  \r -> id ((*) r) r
  \r -> ((*) r) r
  \r -> (*) r r
-}

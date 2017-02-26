{-# LANGUAGE ScopedTypeVariables #-}

module Example where

import Prelude ()
import Zeno

-- Some basic inductive datatypes

data Nat = Zero | Succ Nat
data Tree a = Leaf | Node (Tree a) a (Tree a) 


-- Standard type-classes

class Eq a where
  (==) :: a -> a -> Bool
  
class Eq a => Ord a where
  (<=) :: a -> a -> Bool
  max, min :: a -> a -> a
  
class Num a where
  (+), (-), (*), (^) :: a -> a -> a
  

-- Purely polymorphic functions

id :: a -> a
id x = x 
 
const :: a -> b -> a
const x y = x


-- Boolean functions

not :: Bool -> Bool
not True = False
not False = True

(&&) :: Bool -> Bool -> Bool
True && True = True
_ && _ = False

(||) :: Bool -> Bool -> Bool
False || False = False 
_ || _ = True
  

-- Natural number functions

instance Eq Nat where
  Zero == Zero = True 
  Succ x == Succ y = x == y
  _ == _ = False
  
instance Ord Nat where
  Zero <= y = True
  Succ x <= Zero = False
  Succ x <= Succ y = x <= y
  
  max Zero y = y
  max x Zero = x
  max (Succ x) (Succ y) = Succ (max x y)
  
  min Zero y = Zero
  min x Zero = Zero
  min (Succ x) (Succ y) = Succ (min x y)
  
instance Num Nat where
  Zero + y = y
  Succ x + y = Succ (x + y)

  x - Zero = x
  Zero - y = Zero
  Succ x - Succ y = x - y
  
  Zero * y = Zero
  Succ x * y = y + (x * y)
  
  x ^ Zero = Succ Zero
  x ^ Succ y = x * (x ^ y)

one :: Nat
one = Succ Zero
  

-- List functions

instance Eq a => Eq [a] where
  [] == [] = True
  [] == (_:_) = False
  (_:_) == [] = False
  (x:xs) == (y:ys) = (x == y) && (xs == ys)

length :: [a] -> Nat
length [] = Zero
length (x:xs) = Succ (length xs)

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

reverse :: [a] -> [a]
reverse [] = [] 
reverse (x:xs) = reverse xs ++ [x]

elem :: Eq a => a -> [a] -> Bool
elem _ [] = False
elem n (x:xs) 
  | n == x = True
  | otherwise = elem n xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) 
  | p x = x : xs'
  | otherwise = xs'
  where xs' = filter p xs
  
take :: Nat -> [a] -> [a]
take Zero _ = []
take _ [] = []
take (Succ x) (y:ys) = y : (take x ys) 

drop :: Nat -> [a] -> [a]
drop Zero xs = xs
drop _ [] = []
drop (Succ x) (_:xs) = drop x xs

count :: Nat -> [Nat] -> Nat
count x [] = Zero
count x (y:ys) 
  | x == y = Succ (count x ys)
  | otherwise = count x ys
  
takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile _ [] = []
takeWhile p (x:xs)
  | p x = x : (takeWhile p xs)
  | otherwise = []
    
dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile _ [] = []
dropWhile p (x:xs)
  | p x = dropWhile p xs
  | otherwise = x:xs
  
delete :: Nat -> [Nat] -> [Nat]
delete _ [] = []
delete n (x:xs)
  | n == x = delete n xs
  | otherwise = x : delete n xs
  
map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = f x : map f xs

insert :: Nat -> [Nat] -> [Nat]
insert n [] = [n]
insert n (x:xs)
  | n <= x = n:x:xs
  | otherwise = x : insert n xs

insertsort :: [Nat] -> [Nat]
insertsort [] = []
insertsort (x:xs) = insert x (insertsort xs)

sorted :: [Nat] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys)
  | x <= y = sorted (y:ys)
  | otherwise = False
  

-- Tree functions

height :: Tree a -> Nat
height Leaf = Zero
height (Node l x r) = Succ (max (height l) (height r))

mirror :: Tree a -> Tree a
mirror Leaf = Leaf
mirror (Node l x r) = Node (mirror r) x (mirror l)
  

-- Natural number properties

prop_add_right_ident (x :: Nat)
  = prove (x + Zero :=: x)
prop_add_assoc (x :: Nat) y z
  = prove (x + (y + z) :=: (x + y) + z)
prop_add_commu (x :: Nat) y
  = prove (x + y :=: y + x)

prop_mul_add_dist (x :: Nat) y z
  = prove (x * (y + z) :=: (x * y) + (x * z))
prop_mul_right_ident (x :: Nat)
  = prove (x * one :=: x)
prop_mul_commu (x :: Nat) y
  = prove (x * y :=: y * x)
prop_mul_assoc (x :: Nat) y z
  = prove (x * (y * z) :=: (x * y) * z)
  
prop_leq_ref (x :: Nat)
  = proveBool (x <= x)
prop_leq_trn (x :: Nat) y z
  = givenBool (x <= y)
  $ givenBool (y <= z)
  $ proveBool (x <= z)
prop_leq_total (x :: Nat) y 
  = given (x <= y :=: False)
  $ proveBool (y <= x)
  
prop_max_assoc (x :: Nat) y z
  = prove (max (max x y) z :=: max x (max y z))
prop_min_assoc (x :: Nat) y z 
  = prove (min (min x y) z :=: min x (min y z))

  
-- List properties
  
prop_reverse_twice xs 
  = prove (reverse (reverse xs) :=: xs)
prop_reverse_append xs ys 
  = prove (reverse (xs ++ ys) :=: reverse ys ++ reverse xs)

prop_append_assoc xs ys zs
  = prove ((xs ++ ys) ++ zs :=: xs ++ (ys ++ zs))

prop_length_snoc xs x 
  = prove (length (xs ++ [x]) :=: one + length xs)
prop_length_reverse xs 
  = prove (length (reverse xs) :=: length xs)
prop_length_filter xs p
  = proveBool (length (filter p xs) <= length xs)
prop_length_delete n xs 
  = proveBool (length (delete n xs) <= length xs)
prop_length_drop n xs
  = prove (length (drop n xs) :=: length xs - n)
prop_length_insertsort xs
  = prove (length (insertsort xs) :=: length xs)
  
prop_elem_append_left (n :: Nat) xs ys 
  = givenBool (elem n xs)
  $ proveBool (elem n (xs ++ ys)) 
prop_elem_append_right (n :: Nat) xs ys 
  = givenBool (elem n ys)
  $ proveBool (elem n (xs ++ ys)) 
prop_elem_insert n xs 
  = proveBool (elem n (insert n xs))
prop_elem_insert_eq x y xs 
  = givenBool (x == y)
  $ proveBool (elem x (insert y xs))
  
prop_take_drop_1 n xs ys
  = prove (take n xs ++ drop n xs :=: xs)
prop_take_drop_2 n m xs 
  = prove (drop n (take m xs) :=: take (m - n) (drop n xs))
prop_drop_map f n xs 
  = prove (drop n (map f xs) :=: map f (drop n xs))
prop_take_map f n xs
  = prove (take n (map f xs) :=: map f (take n xs))
prop_drop_drop n m xs 
  = prove (drop n (drop m xs) :=: drop (n + m) xs)
  
prop_filter_app p xs ys 
  = prove (filter p (xs ++ ys) :=: filter p xs ++ filter p ys)

prop_count_add_app n xs ys
  = prove (count n xs + count n ys :=: count n (xs ++ ys))
prop_count_leq_app n xs ys
  = proveBool (count n xs <= count n (xs ++ ys))
prop_count_snoc n xs
  = prove (Succ (count n xs) :=: count n (xs ++ [n]))
prop_count_reverse n xs 
  = prove (count n (reverse xs) :=: count n xs)
prop_count_insertsort n xs
  = prove (count n (insertsort xs) :=: count n xs)
  
prop_insert_sorts (x :: Nat) xs
  = givenBool (sorted xs)
  $ proveBool (sorted (insert x xs))
prop_insertsort_sorts (xs :: [Nat]) 
  = proveBool (sorted (insertsort xs))
prop_insertsort_idem xs 
  = prove (insertsort (insertsort xs) :=: insertsort xs)
  
  
-- Tree properties
-- Grounding the polymorphic type to Bool means these are solved more quickly

prop_height_mirror (t :: Tree Bool) 
  = prove (height t :=: height (mirror t))
prop_mirror_twice (t :: Tree Bool)
  = prove (mirror (mirror t) :=: t)

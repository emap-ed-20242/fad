import Fad.Chapter1

namespace Chapter7

-- 7.1 A generic greedy algorithm

def NonEmptyList (α : Type) : Type :=
 {l : List α // l.length > 0}

def foldr1₀ (f : a → a → a) (as : NonEmptyList a) : a :=
  let x := as.val.head (List.ne_nil_of_length_pos as.property)
  if h₂ : as.val.length = 1 then
    x
  else
    let as' := as.val.tail
    have : as.val.length - 1 < as.val.length := by
      have h₁ := as.property; omega
    f x (foldr1₀ f (Subtype.mk as' (by
      -- change as.val.tail.length > 0
      have h₁ := as.property
      rw [List.length_tail]
      omega)))
termination_by as.val.length

#eval foldr1₀ (fun a b => a + b ) (Subtype.mk [1,2,3,4,5,6] (by simp))


def foldr1₁ (f : a → a → a) (as : List a) (h : as.length > 0 := by decide) : a :=
  let x := as.head (List.ne_nil_of_length_pos h)
  if h₂ : as.length = 1 then
    x
  else
    f x (foldr1₁ f as.tail (by rw [List.length_tail]; omega))

#eval foldr1₁ (fun a b => a + b ) [1,2,3]


def foldr1 [Inhabited a] (f : a → a → a) : List a → a
  | []    => default
  | [x]   => x
  | x::xs => f x (foldr1 f xs)

example : foldr1 (fun a b => a + b ) [1,2,3] = 6 := rfl

def minWith { a b : Type} [LE b] [Inhabited a] [DecidableRel (@LE.le b _)]
  (f : a → b) (as : List a) : a :=
  let smaller f x y := if f x ≤ f y then x else y
  foldr1 (smaller f) as


-- 7.2 Greedy sorting algorithms

open Chapter1 (tails) in

def pairs (xs : List a) : List (Prod a a) :=
 let step₁ : List a → List (Prod a a) → List (Prod a a)
  | [], acc => acc
  | x::ys, acc =>
    let step₂ : List a → List (Prod a a) → List (Prod a a)
     | [], acc => acc
     | y::_, acc => (x, y) :: acc
    (tails ys).foldr step₂ acc
 (tails xs).foldr step₁ []


def ic [LT a] [DecidableRel (@LT.lt a _)]
 (xs : List a) : Nat :=
 (pairs xs).filter (λ p => p.1 > p.2) |>.length


def extend : a → List a → List (List a)
| x, []      => [[x]]
| x, (y::xs)  => (x :: y :: xs) :: (extend x xs).map (y:: ·)


open Chapter1 in

def perms : List a → List (List a) :=
 List.foldr (concatMap ∘ extend) [[]]

def sort [LT a] [DecidableRel (@LT.lt a _)]
  : List a → List a :=
  minWith ic ∘ perms

#eval sort [3, 1, 4, 2, 7, 4]

def gstep [LT a] [DecidableRel (@LT.lt a _)]
  (x : a) : List a → List a :=
  (minWith ic) ∘ extend x

#eval gstep 0 [7,1,2,3]


end Chapter7

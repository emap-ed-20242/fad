
namespace Chapter1

-- 1.1 Basic types and functions

def map : (a → b) → List a → List b
| _, [] => []
| f, (x :: xs) => f x :: map f xs

#eval map (· * 10) [1,2,3]
#eval map (λ x => x * 10) [1,2,3]

def filter {a : Type}  : (a → Bool) → List a → List a
| _, [] => []
| p, (x :: xs) => if p x then x :: filter p xs else filter p xs

#eval filter (· > 5) [1,2,2,4,5,8,6]

def foldr {a b : Type} : (a → b → b) → b → List a → b
| _, e, [] => e
| f, e, (x::xs) => f x (foldr f e xs)

def foldl {a b : Type} : (b → a → b) → b → List a → b
| _, e, [] => e
| f, e, (x::xs) => foldl f (f e x) xs

def length : List a → Nat := foldr succ 0
  where succ _ n := n + 1

example : length ["a", "b", "c"] = 3 := by
  unfold length
  unfold foldr
  unfold foldr
  unfold foldr
  rewrite [length.succ]
  rewrite [length.succ]
  rewrite [length.succ]
  unfold foldr
  rfl

example : foldr Nat.add 0 [1,2,3] = 6 := by
  unfold foldr
  unfold foldr
  unfold foldr
  unfold foldr
  rewrite (config := {occs := .pos [3]}) [Nat.add]
  rewrite (config := {occs := .pos [2]}) [Nat.add]
  rewrite (config := {occs := .pos [1]}) [Nat.add]
  rfl

example : foldl Nat.add 0 [1,2,3] = 6 := by
  unfold foldl
  unfold foldl
  unfold foldl
  unfold foldl
  rewrite (config := {occs := .pos [3]}) [Nat.add]
  rewrite (config := {occs := .pos [2]}) [Nat.add]
  rewrite (config := {occs := .pos [1]}) [Nat.add]
  rfl

-- 1.2 Processing lists

def concat1 {a : Type} : List (List a) → List a :=
 List.foldr List.append []

def concat2 {a : Type} : List (List a) → List a :=
 List.foldl List.append []

example : concat1 [[1,2,3,4], [5], [6]] = [1,2,3,4,5,6] := by
  unfold concat1
  unfold List.foldr
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  unfold List.foldr
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  unfold List.foldr
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  unfold List.foldr
  rfl

example : concat2 [[1,2,3,4], [5], [6]] = [1,2,3,4,5,6] := by
  unfold concat2
  unfold List.foldl
  rw [List.append.eq_1]
  unfold List.foldl
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  unfold List.foldl
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  unfold List.foldl
  rfl

open List in
example : ∀ xs : List Nat, foldr cons [] xs = xs := by
  intro xs
  induction xs with
  | nil => unfold foldr; rfl
  | cons h1 h2 ih => unfold foldr; rewrite [ih]; rfl


-- 1.3 Inductive and recursive definitions

def inserts {a : Type} : a → List a → List (List a)
| x, [] => [[x]]
| x, (y :: ys) => (x :: y :: ys) :: map (y :: ·) (inserts x ys)

#eval inserts 1 [2,3]

def concatMap (f : a → List b) : List a → List b := concat1 ∘ (map f)

def perm₁ : List a → List (List a) :=
  let step x xss := concatMap (inserts x) xss
  foldr step [[]]

#eval perm₁ "123".toList |>.map List.asString


end Chapter1

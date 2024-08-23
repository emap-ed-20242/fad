
namespace Chapter1

-- 1.1 Basic types and functions

def map : (a → b) → List a → List b
| _, [] => []
| f, (x :: xs) => f x :: map f xs

#eval map (· * 10) [1,2,3]

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

#eval foldr (fun a b => a + b) 0 [1,2,3]

theorem test₁ : foldr Nat.add 0 [1,2,3] = 6 := by
  unfold foldr
  unfold foldr
  unfold foldr
  unfold foldr
  rfl -- can I do only beta-reduction?

theorem test₂ : foldl Nat.add 0 [1,2,3] = 6 := by
  unfold foldl
  unfold foldl
  unfold foldl
  unfold foldl
  rfl -- can I do only beta-reduction?

-- 1.2 Processing lists

def concat1 {a : Type} (xss : List (List a)) : List a :=
 List.foldr List.append [] xss

def concat2 (xss : List (List a)) : List a :=
 List.foldl List.append [] xss

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

theorem foldrEmptyAll : ∀ xs : List Nat, foldr List.cons [] xs = xs := by
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


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


def scanl : (b → a → b ) → b → List a → List b
| _, e, [] => [e]
| f, e, (x :: xs) => e :: scanl f (f e x) xs

#eval scanl Nat.add 0 [1,2,3,4]
#eval scanl Nat.add 42 []
#eval scanl (λ r n => n :: r) "foo".toList ['a', 'b', 'c', 'd'] |>.map List.asString


-- 1.3 Inductive and recursive definitions

-- https://stackoverflow.com/a/20414229/121095

def inserts {a : Type} : a → List a → List (List a)
| x, [] => [[x]]
| x, (y :: ys) => (x :: y :: ys) :: map (y :: ·) (inserts x ys)

#eval inserts 1 [2,3]

def concatMap (f : a → List b) : List a → List b := concat1 ∘ (List.map f)

def perm₁ : List a → List (List a) :=
  let step x xss := concatMap (inserts x) xss
  foldr step [[]]

#eval perm₁ "123".toList |>.map List.asString

example (x : Nat) (xss : List (List Nat))
 : concatMap (inserts x) xss = (concatMap ∘ inserts) x xss := by
  unfold concatMap
  rewrite [Function.comp]
  rewrite [Function.comp]
  rewrite [Function.comp]
  rfl

def perm₁' : List a → List (List a) :=
  foldr (concatMap ∘ inserts) [[]]


def picks {a : Type} : List a → List (a × List a)
| [] => []
| (x :: xs) =>
   (x, xs) :: ((picks xs).map (λ p => (p.1, x :: p.2)))

#eval picks [1,2,3]

def perm₂ : List a → List (List a)
  | [] => [[]]
  | xs => concatMap (λ p => (perm₂ p.2).map (p.1 :: ·)) (picks xs)
 termination_by xs => xs.length

theorem perm_aux {a : Type}
  (v : a) (l : List a)
  (p : a × List a) (h : p ∈ picks (v :: l)) :
  p.2.length < (v :: l).length := by
  induction l with
  | nil =>
     unfold picks at h
     rw [picks.eq_1] at h
     rw [List.map.eq_1] at h
     simp; simp at h; rw [h]; simp; done
  | cons x xs ih => sorry

def perm : List a → List (List a)
  | [] => [[]]
  | x :: xs => concatMap (fun ⟨p, hp⟩ ↦
      have : p.2.length < (x :: xs).length := perm_aux x xs p hp
      (perm p.2).map (p.1 :: ·))
      (picks (x :: xs)).attach
 termination_by xs => xs.length

partial def until' (p: a → Bool) (f: a → a) (x : a) : a :=
  if p x then x
  else until' p f (f x)

partial def while' (p : a → Bool) := until' (not ∘ p)

#eval while' (· < 10) (· + 1) 0


-- 1.4 Fusion

example {a b c : Type} (f : b → c) (g : a → b) : map f ∘ map g = map (f ∘ g) := by
  funext xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Function.comp, map]; rw [← ih]; rfl

theorem append_left_nil : ∀ xs : List a, [] ++ xs = xs := by
 intro h1
 induction h1 with
 | nil => rfl
 | cons ha hs => simp [List.append]; done

example (xs ys : List a) (f : a → b → b) (e : b)
 : foldr f e (xs ++ ys) = foldr f (foldr f e ys) xs := by
  have h1 := append_left_nil ys
  induction xs with
  | nil => rw [foldr.eq_1]; rewrite [h1]; rfl
  | cons x xs ih => simp [List.append, foldr]; rw [ih]

example (f : a → a → a)
 : foldr f e ∘ concat1 = foldr (flip (foldr f)) e := by
  funext xs
  induction xs with
  | nil =>
    rw [foldr.eq_1, Function.comp]
    simp [concat1, foldr.eq_1]
  | cons x xs ih =>
    rw [foldr]
    rw [← ih]
    rw [Function.comp]
    rw [concat1]
    simp [foldr.eq_2]
    sorry

example (g : a → b → b) (h : a → b) (h₁ : ∀ x y, h (f x y) = g x (h y))
 : h (foldr f e xs) = foldr g (h e) xs := by
 induction xs with
  | nil =>
    rewrite [foldr.eq_1]
    rewrite [foldr.eq_1]
    rfl
  | cons x xs ih =>
    rewrite [foldr]
    rewrite [h₁ x (foldr f e xs)]
    rewrite [ih]
    rewrite [foldr]
    rfl


-- 1.5 Accumulating and tupling


end Chapter1

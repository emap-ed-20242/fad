
import Fad.Chapter1

namespace Chapter1Ex
open Chapter1


def dropWhile {α : Type} (p : α → Bool) : (xs : List α) -> List α
| [] => []
| (x :: xs) => if p x then dropWhile p xs else x :: xs

#eval dropWhile (· < 5) []
#eval dropWhile (· < 5) (List.iota 10).reverse


def uncons {α : Type} (xs : List α) : Option (α × List α) :=
  match xs with
  | [] => none
  | x :: xs => some (x, xs)

example : uncons ([] : List Nat) = none := rfl
example : uncons [1] = some (1, []) := rfl
example : uncons [1, 2] = some (1, [2]) := rfl
example : uncons [1, 2, 3, 4, 5] = some (1, [2, 3, 4, 5]) := rfl


def wrap {α : Type} (a : α) : List α := [a]

example : wrap 0 = [0] := rfl
example : wrap [42] = [[42]] := rfl


def unwrap {α : Type} (a : List α) : Option α :=
  match a with
  | [x] => some x
  | _ => none

example : unwrap [42] = some 42 := rfl
example : unwrap [0, 1] = none := rfl
example : unwrap (@List.nil Nat) = none := rfl


def single {α : Type} (a : List α) : Bool :=
  match a with
  | [_] => true
  | _   => false

example : single [42] = true := rfl
example : single [0, 1] = false := rfl
example : single ([] : List Nat) = false := rfl

theorem single_aux {x : Nat} {xs : List Nat}
  : single (x :: xs) = true ↔ xs = [] := by
  cases xs with
  | nil => simp [single]
  | cons a xs => simp [single]

example : ∀ xs : List Nat, single xs = true ↔ xs.length = 1 := by
  intro xs
  induction xs with
  | nil => simp [single]
  | cons x xs _ =>
    rw [single_aux]
    simp [List.length]


def reverse {α : Type} (a : List α) : List α :=
  let rec helper (a : List α) (res : List α) : List α :=
    match a with
    | [] => res
    | x :: xs => helper xs (x :: res)
  helper a []

example : reverse [3, 4, 5] = [5, 4, 3] := rfl
example : reverse ([] : List Nat) = [] := rfl


example (f : α → β → β) :
 (foldr f e) ∘ (filter p) = foldr (λ x y => if p x then f x y else y) e
 := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>

    rw [Function.comp]
    rw [filter]
    by_cases h : p y = true
    rw [if_pos h]
    rw [foldr]
    rw [foldr]
    rw [if_pos h]
    have lh : ((foldr f e) ∘ (filter p)) (ys) = foldr f e (filter p (ys)) := by rw [Function.comp]
    rewrite [←lh]
    exact congrArg (f y) ih

    rw [if_neg h]
    rw [foldr]
    rw [if_neg h]
    have lh : ((foldr f e) ∘ (filter p)) (ys) = foldr f e (filter p (ys)) := by rw [Function.comp]
    rewrite [←lh]
    exact ih


def takeWhile {α : Type} (p : α → Bool) : (xs : List α) -> List α :=
  List.foldr helper []
 where helper (x : α) (xs : List α) : List α :=
   if p x then x :: xs else []

example : takeWhile (· < 3) [1, 2, 3, 4] = [1, 2] := by
  rw [takeWhile]
  rw [List.foldr]; rw [takeWhile.helper]
  rw [List.foldr]; rw [takeWhile.helper]
  rw [List.foldr]; rw [takeWhile.helper]
  rw [List.foldr]; rw [takeWhile.helper]
  rw [List.foldr]; rfl

#eval takeWhile (· > 5) []
#eval takeWhile (· < 5) [4, 7, 8]

theorem map_compose {α β γ : Type} (f : β → γ) (g : α → β) (l : List α) :
  map (f ∘ g) l = map f (map g l) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
  simp [map, ih]

theorem foldl_comp {a b: Type} (y: a) (e : b) (f : b → a → b):
foldl f e ∘ (fun x => y :: x) = foldl f (f e y) := by rfl

theorem map_equal (a : List α) (f : α → β): map f a = List.map f a := by
induction a with
| nil => rfl
| cons a as ih =>
  simp
  rw [map]
  exact congrArg (List.cons (f a)) ih


example (f : α → β → α) : map (foldl f e) ∘ inits = scanl f e := by
  funext xs
  induction xs generalizing e with
  | nil => exact rfl
  | cons y ys ih =>
  rw [Function.comp]
  rw [inits]
  rw [scanl]
  rw [map]
  simp [foldl]
  rw [←map_equal]
  rw [←map_compose]
  rw [foldl_comp]
  have h : map (foldl f (f e y)) (inits ys) = (map (foldl f (f e y)) ∘ inits) ys := by rfl
  rw [h]
  exact ih

example (f : α → β → β) : map (foldr f e) ∘ tails = scanr f e := sorry


def steep₁ (xs : List Nat) : Bool :=
  let rec sum : List Nat → Nat
   | [] => 0
   | x :: xs  => x + sum xs
  match xs with
  | []  => true
  | x :: xs => x > sum xs ∧ steep₁ xs


def steep₂ : List Nat → Bool :=
 Prod.snd ∘ faststeep
 where
  faststeep : List Nat → (Nat × Bool)
  | [] => (0, true)
  | x :: xs =>
    let (s, b) := faststeep xs
    (x + s, x > s ∧ b)

example : steep₁ [8,4,2,1] = steep₂ [8,4,2,1] := rfl
example : steep₁ [] = steep₂ [] := rfl

example : ∀ xs, steep₁ xs = steep₂ xs := sorry


/-
| 1.11 | Carlos César de Oliveira Fonseca       |
-/

end Chapter1Ex

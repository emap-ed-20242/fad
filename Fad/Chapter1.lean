
namespace Chapter1

-- 1.1 Basic types and functions

def map : (a → b) → List a → List b
| _, [] => []
| f, (x :: xs) => f x :: map f xs

#eval map (· * 10) [1,2,3] = [10,20,30]
#eval map (λ x => x * 10) [1,2,3] = [10,20,30]

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

def length' (xs : List a) : Nat :=
  foldr (fun _ y => y + 1) 0 xs

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
  rewrite [foldr.eq_1]
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
  | cons a as ih => unfold foldr; rewrite [ih]; rfl


def scanl : (b → a → b ) → b → List a → List b
| _, e, [] => [e]
| f, e, (x :: xs) => e :: scanl f (f e x) xs

#eval scanl Nat.add 0 [1,2,3,4]
#eval scanl Nat.add 42 []
#eval scanl (λ r n => n :: r)
  "foo".toList ['a', 'b', 'c', 'd'] |>.map List.asString

def inits {a : Type} : List a → List (List a)
| [] => [[]]
| (x :: xs) => [] :: (inits xs).map (fun ys => x :: ys)

def tails {a : Type} : List a → List (List a)
| [] => [[]]
| (x :: xs) => (x :: xs) :: tails xs

theorem map_compose {α β γ : Type} (f : β → γ) (g : α → β) (l : List α) :
  map (f ∘ g) l = map f (map g l) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
  simp [map, ih]

theorem foldl_comp {α β: Type} (y: α) (e : β) (f : β → α → β):
foldl f e ∘ (fun x => y :: x) = foldl f (f e y) := by rfl

theorem map_map {α : Type} (g : α -> α ) (a : List α): List.map g a = map g a := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    rw [map,List.map]
    rw [ih]
    done

example {a b : Type} (f : b → a → b) (e : b) :
   map (foldl f e) ∘ inits = scanl f e := by
  funext xs
  induction xs generalizing e with
  | nil => simp [map, inits, foldl, scanl]
  | cons x xs ih =>
    rw [Function.comp]
    rw [inits,map,foldl,map_map,←map_compose]
    rw [foldl_comp,scanl]
    have hx := ih (f e x)
    rw [← hx]
    simp

-- 1.3 Inductive and recursive definitions

def inserts {a : Type} : a → List a → List (List a)
| x, [] => [[x]]
| x, (y :: ys) => (x :: y :: ys) :: map (y :: ·) (inserts x ys)

#eval inserts 1 [2,3,4,5]

def concatMap (f : a → List b) : List a → List b :=
 concat1 ∘ (List.map f)

#eval concatMap (String.toList ·) ["aa", "bb", "cc"]

def perm₀ : List a → List (List a)
 | [] => [[]]
 | (x :: xs) => concatMap (inserts x ·) (perm₀ xs)

def perm₁ : List a → List (List a) := foldr step [[]]
 where
  step x xss := concatMap (inserts x) xss

example (x : Nat)
 : concatMap (inserts x) = (concatMap ∘ inserts) x := by
  unfold concatMap
  rewrite [Function.comp]
  rfl

def perm₁' : List a → List (List a) :=
  foldr (concatMap ∘ inserts) [[]]

#eval perm₁ "12".toList |>.map List.asString


def picks {a : Type} : List a → List (a × List a)
| [] => []
| (x :: xs) =>
   (x, xs) :: ((picks xs).map (λ p => (p.1, x :: p.2)))

theorem picks_less :
  p ∈ picks xs → p.2.length < xs.length := by
  induction xs with
  | nil =>
    unfold picks
    intro h
    simp at h
  | cons x xs ih =>
    intro h
    unfold picks at h
    simp at h
    cases h with
    | inl h =>
      rw [h]
      simp
    | inr h =>
      simp; rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq]; left; apply ih
      apply Exists.elim h; intro q hq; sorry


partial def perm₂ : List a → List (List a)
  | [] => [[]]
  | xs => concatMap  (λ p => (perm₂ p.2).map (p.1 :: ·)) (picks xs)


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

#eval until' (· > 10) (· + 1) 0


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

theorem foldr_append {α β : Type} (f : α → β → β) (e : β) (xs ys : List α) :
  foldr f e (xs ++ ys) = foldr f (foldr f e ys) xs := by
  induction xs with
  |nil => rfl
  |cons x xs ih =>
    simp [foldr, ih]

example (f : a → a → a)
 : foldr f e ∘ concat1 = foldr (flip (foldr f)) e := by
  funext xs
  induction xs with
  | nil =>
    rw [foldr.eq_1, Function.comp]
    simp [concat1, foldr.eq_1]
  | cons y ys ih =>
    rw [Function.comp]
    simp [concat1]
    rw [←concat1]
    rw [foldr_append]
    rw [foldr]
    rw [flip]
    exact congrArg (λ x => foldr f x y) ih

theorem fusion_th (g : a → b → b) (h : a → b) (h₁ : ∀ x y, h (f x y) = g x (h y))
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

def sum (xs : List Int) := xs.foldl Int.add 0

partial def collapse₀ (xss : List (List Int)) : List Int :=
 help [] xss
 where
  help : List Int → List (List Int) → List Int
  | xs, xss =>
    if (sum xs) > 0 ∨ xss.isEmpty then xs
    else help (xs.append xss.head!) xss.tail

def collapse₁ (xss : List (List Int)) : List Int :=
 help [] xss
 where
  help : List Int → List (List Int) → List Int
  | xs, [] => xs
  | xs, (as :: bss) =>
    if (sum xs) > 0 then xs
    else help (xs.append as) bss

partial def collapse₂ (xss : List (List Int)) : List Int :=
  help (0, []) (labelsum xss)
  where
   labelsum (xss : List (List Int)) : List (Int × List Int) :=
     List.zip (map sum xss) xss
   help : (Int × List Int) → List (Int × List Int) → List Int
   | (_, xs), [] => xs
   | (s, xs), xss => if s > 0 then xs else help (cat (s, xs) xss.head!) xss.tail
   cat : (Int × List Int) → (Int × List Int) → (Int × List Int)
   | (s, xs), (t, ys) => (s + t, xs ++ ys)

def collapse₃ (xss : List (List Int)) : List Int :=
  help (0, id) (labelsum xss) []
  where
    labelsum (xss : List (List Int)) : List (Int × List Int) :=
     List.zip (map sum xss) xss
    help :
    let tf := List Int → List Int
    (Int × tf) → List (Int × List Int) → tf
    | (_, f), [] => f
    | (s, f), (as :: bs) =>
      if s > 0 then f
      else help (s + as.1, f ∘ (as.2 ++ ·)) bs

#eval collapse₃ [[1],[-3],[2,4]]
#eval collapse₃ [[-2,1],[-3],[2,4]]
#eval collapse₃ [[-2,1],[3],[2,4]]


def fib : Nat → Nat
  | 0     => 1
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n + 2) = fib (n + 1) + fib n := rfl
example : fib 7 = 21 := rfl

def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
  | 0   => (0, 1)
  | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100
#reduce fib 100 -- try eval
#print fib

example : fibFast 4 = 5 := by
  unfold fibFast
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  rfl


-- Exercicios

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
  | cons x xs ih =>
    rw [single_aux]
    simp [List.length]
    done


def reverse {α : Type} (a : List α) : List α :=
  let rec helper (a : List α) (res : List α) : List α :=
    match a with
    | [] => res
    | x :: xs => helper xs (x :: res)
  helper a []

example : reverse [3, 4, 5] = [5, 4, 3] := rfl
example : reverse ([] : List Nat) = [] := rfl

/-
example : (foldr f e) ∘ (filter p) = foldr ???? := sorry

/- as an instance of foldr -/
def takeWhile (xs : List α) (p : α → Bool) : List α := sorry

example : map (foldl f e) ∘ inits = ????  := sorry

example : map (foldr f e) ∘ tails = ???? := sorry

/- determining whether a sequence of numbers is steep. Ex 1.21 -/
def steep₁ (xs : List Nat) : Bool := sorry

/- determining whether a sequence of numbers is steep. Ex 1.21 using tupling -/
def steep₂ (xs : List Nat) : Bool := sorry
-/

end Chapter1

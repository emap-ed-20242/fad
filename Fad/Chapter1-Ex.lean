import Fad.Chapter1

namespace Chapter1

/- # Exercicio 1.1 -/

def dropWhile (p : α → Bool) : (xs : List α) -> List α
| [] => []
| (x :: xs) => if p x then dropWhile p xs else x :: xs


/- # Exercicio 1.2 -/

def uncons {α : Type} (xs : List α) : Option (α × List α) :=
  match xs with
  | [] => none
  | x :: xs => some (x, xs)


/- # Exercicio 1.3 -/

def wrap {α : Type} (a : α) : List α := [a]

example : wrap 0 = [0] := rfl
example : wrap [42] = [[42]] := rfl

def unwrap {α : Type} (a : List α) : Option α :=
  match a with
  | [x] => some x
  | _   => none

def unwrap! {α : Type} [Inhabited α]  : (a : List α) → α
 | [x] => x
 | _   => panic! "unwrap!: empty list"

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


/- # Exercicio 1.4 -/

def reverse₀ {α : Type} (a : List α) : List α :=
  let rec helper (a : List α) (res : List α) : List α :=
    match a with
    | [] => res
    | x :: xs => helper xs (x :: res)
  helper a []

def reverse₁ {a : Type} : List a → List a :=
 List.foldl (flip List.cons) []

theorem aux_rev_append {α : Type} (as bs: List α)
 : List.foldl (flip List.cons) as bs = (List.foldl (flip List.cons) [] bs) ++ as := by
  induction bs generalizing as with
    | nil => rfl
    | cons c cs ih =>
      rw [List.foldl, flip]
      rw [List.foldl, flip]
      rw [ih, ih [c]]
      simp

theorem rev_cons : reverse₁ (x :: xs) = reverse₁ xs ++ [x] := by
  rw (occs := .pos [1]) [reverse₁]
  rw [List.foldl, flip]
  rw [aux_rev_append]
  rfl

theorem rev_append {α : Type} (as bs: List α) :
reverse₁ (as ++ bs) = reverse₁ bs ++ reverse₁ as := by
  induction as generalizing bs with
    | nil => simp; rfl
    | cons c cs ih =>
      rw [List.cons_append]
      rw [rev_cons, rev_cons, ← List.append_assoc]
      rw [ih]

theorem reverse_reverse {α : Type}  (xs : List α)
 : reverse₁ (reverse₁ xs) = xs := by
 induction xs with
 | nil => rfl
 | cons a as ih =>
   rw [rev_cons]
   rw [rev_append]
   rw [ih]; simp [reverse₁, flip]


/- # Exercicio 1.5 -/

def map' {α β : Type} (f : α → β) (xs : List α) : List β :=
  let op x xs := f x :: xs
  List.foldr op [] xs

def filter' {α : Type} (p : α → Bool) (xs : List α) : List α :=
  let op x xs := if p x then x :: xs else xs
  List.foldr op [] xs


/- # Exercicio 1.6 -/

theorem foldr_filter_aux :
 (foldr f e ∘ filter p) ys = foldr f e (filter p ys) := by
 rfl

example (f : α → β → β)
 : foldr f e ∘ filter p = foldr (λ x y => if p x then f x y else y) e
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
    rewrite [←foldr_filter_aux]
    exact congrArg (f y) ih
    rw [if_neg h]
    rw [foldr]
    rw [if_neg h]
    rewrite [←foldr_filter_aux]
    exact ih


/- # Exercicio 1.7 -/

def takeWhile {α : Type} (p : α → Bool) : List α → List α :=
  let op x acc := if p x then x :: acc else []
  List.foldr op []

example : takeWhile (fun x => x % 2 = 0) [2, 3, 4, 5] = [2] := by
  rw [takeWhile]
  rw [List.foldr]
  rw [List.foldr]
  rw [List.foldr]
  rw [List.foldr]
  rw [List.foldr]
  rfl


/- # Exercicio 1.8 -/

def dropWhileEnd {α : Type} (p : α → Bool) (xs : List α) : List α :=
 let op x xs := if p x ∧ xs.isEmpty then [] else x :: xs
 xs.foldr op []



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

example (f : α → β → β) : map (foldr f e) ∘ tails = scanr f e := by
  funext xs
  induction xs with
  | nil =>
    simp [Function.comp]
    simp [tails,map,scanr,foldr]
  | cons y ys ih =>
    sorry


/- # Exercicio 1.11 -/

def integer: List Nat → Nat :=
  List.foldl shiftl 0
  where
   shiftl (n d : Nat) : Nat := 10 * n + d

def fraction : List Nat → Float :=
  List.foldr shiftr 0
  where
  shiftr (d : Nat) (n : Float) : Float := (d.toFloat + n)/10

/- # Exercicio 1.13 -/

def apply {a : Type} : Nat → (a → a) → a → a
 | 0, _     => id
 | n + 1, f => f ∘ apply n f

def apply₁ {a : Type} : Nat → (a → a) → a → a
 | 0, _     => id
 | n + 1, f => apply n f ∘ f


/- # Exercicio 1.14 -/

def inserts₁ {a : Type} (x : a) (ys : List a) : List (List a) :=
  let step y yss :=
    (x :: y :: (yss.head!.tail)) :: yss.map (y :: ·)
  ys.foldr step [[x]]


/- # Exercicio 1.15 -/

def remove {α : Type} [DecidableEq α] (x : α) : List α → List α
| []        => []
| (y :: ys) => if x = y then ys else y :: remove x ys

partial def perms₃ {α : Type} [DecidableEq α] : List α → List (List α)
| []  => [[]]
| as  =>
  as.flatMap (λ x => (perms₃ (remove x as)).map (λ ys => x :: ys))


/- # Exercicio 1.20 -/

def concat {α : Type} (xss : List (List α)) : List α :=
  let op f (xs ys : List α) : List α := f (xs ++ ys)
  List.foldl op id xss []

example : concat [[1, 2], [3, 4]] = [1, 2, 3, 4] := by
  rw [concat]
  rewrite [List.foldl]
  rewrite [List.foldl]
  rewrite [List.foldl]
  rfl

/- # Exercicio 1.21 -/

-- set_option trace.profiler true

def steep₀ (xs : List Nat) : Bool :=
  let sum (xs : List Nat) : Nat :=
    xs.foldl (· + ·) 0
  match xs with
  | []  => true
  | x :: xs => x > sum xs ∧ steep₀ xs

-- #eval steep₀ (List.iota 10000000)

def steep₁ (xs : List Nat) : Bool :=
  let rec sum : List Nat → Nat → Nat
   | [], s => s
   | x :: xs, s  => sum xs (x + s)
  match xs with
  | []  => true
  | x :: xs => x > sum xs 0 ∧ steep₁ xs

-- #eval steep₁ (List.iota 10000000)

def steep₂ : List Nat → Bool :=
 Prod.snd ∘ faststeep
 where
  faststeep : List Nat → (Nat × Bool)
  | [] => (0, true)
  | x :: xs =>
    let (s, b) := faststeep xs
    (x + s, x > s ∧ b)

-- #reduce steep₂ (List.range 100000) stack overflow

def steep₃ : List Nat → Bool :=
 Prod.snd ∘ faststeep
 where
  faststeep (xs : List Nat) : (Nat × Bool) :=
   xs.reverse.foldl (λ t x => (x + t.1, x > t.1 ∧ t.2) ) (0, true)

-- #eval steep₃ [8,5,2]
-- #eval steep₃ (List.range 100000)

example : steep₁ [8,4,2,1] = steep₂ [8,4,2,1] := rfl
example : steep₁ [] = steep₂ [] := rfl

example : ∀ xs, steep₁ xs = steep₂ xs := sorry


end Chapter1


namespace Chapter5

namespace S51 -- Quicksort

inductive Tree a where
| null : Tree a
| node : (Tree a) → a → (Tree a) → Tree a

def mkTree [LT a] [DecidableRel (α := a) (· < ·)] : List a → Tree a
| [] => Tree.null
| x :: xs =>
  let p := xs.partition (. < x)
  Tree.node (mkTree p.1) x (mkTree p.2)
 termination_by l => l.length
 decreasing_by
  all_goals simp
   [List.partition_eq_filter_filter,
    List.length_filter_le,
    Nat.lt_add_one_of_le]

def Tree.flatten : Tree a → List a
| null => []
| node l x r => l.flatten ++ [x] ++ r.flatten

def qsort₀ [LT a] [DecidableRel (α := a) (· < ·)] : List a → List a :=
 Tree.flatten ∘ mkTree

def qsort₁ [h₁ : LT a] [h₂ : DecidableRel (α := a) (· < ·)] : List a → List a
 | [] => []
 | (x :: xs) =>
  let p := xs.partition (· < x)
  (qsort₁ p.1) ++ [x] ++ (qsort₁ p.2)
 termination_by xs => xs.length
 decreasing_by
  all_goals simp
   [List.partition_eq_filter_filter,
    List.length_filter_le,
    Nat.lt_add_one_of_le]

/-
#eval qsort₀ (List.iota 145)
#eval qsort₁ (List.iota 145)
#eval qsort₁ ['c','b','a']
-/

structure Person where
  name : String
  age : Nat

instance : LT Person where
  lt p q := p.age < q.age

def people := [
  Person.mk "Alice" 23,
  Person.mk "Bob" 25,
  Person.mk "Eve" 22]

-- #eval qsort₁ people (how to fix this? PENDING)

end S51

namespace S52 -- Mergesort

inductive Tree (α : Type) : Type where
 | null : Tree α
 | leaf : α → Tree α
 | node : Tree α → Tree α → Tree α
 deriving Repr, Inhabited

def merge [LE a] [DecidableRel (α := a) (· ≤ ·)]
: List a → List a → List a
| [], ys => ys
| xs, [] => xs
| (x :: xs), (y :: ys) =>
  if x ≤ y then
   x :: merge xs (y :: ys)
  else
   y :: merge (x :: xs) ys

def flatten [LE a] [DecidableRel (· ≤ · : a → a → Prop)]
: Tree a → List a
| Tree.null   => []
| Tree.leaf x => [x]
| Tree.node l r => merge (flatten l) (flatten r)


def halve₀ (xs : List a) : (List a × List a) :=
 let m := xs.length / 2
 (xs.take m,xs.drop m)

def halve₁ : (xs : List a) → (List a × List a) :=
 let op x p := (p.2, x :: p.1)
 List.foldr op ([],[])

-- inspirado em:
-- https://github.com/leanprover-community/mathlib4/blob/8666bd82efec40b8b3a5abca02dc9b24bbdf2652/Mathlib/Init/Data/Nat/Lemmas.lean#L482-L486

def twoStepInduction {P : List a → Prop}
  (empty : P [])
  (single : ∀ as, as.length = 1 → P as)
  (more : ∀ a b as, P as → P (a :: b :: as)) : ∀ as, P as
  | [] => empty
  | a :: [] => single [a] (by simp)
  | a :: b :: cs => more _ _ _ (twoStepInduction empty single more _)

theorem length_halve_fst : (halve₁ xs).fst.length = xs.length / 2 := by
induction xs using twoStepInduction with
| empty => simp [halve₁]
| single a h =>
  have _ :: [] := a
  simp [halve₁]
| more a b cs ih =>
  rw [halve₁, List.foldr, List.foldr, <-halve₁]
  simp
  omega

theorem length_halve_snd : (halve₁ xs).snd.length = (xs.length + 1) / 2 := by
induction xs using twoStepInduction with
| empty => simp [halve₁]
| single a h =>
  have _ :: [] := a
  simp [halve₁]
| more a b cs ih =>
  rw [halve₁, List.foldr, List.foldr, <-halve₁]
  simp
  omega

def mkTree : (as : List a) → Tree a
| [] => Tree.null
| x :: xs =>
  if h: xs.length = 0 then Tree.leaf x
  else
    let p := halve₁ (x :: xs)
    have : (halve₁ (x :: xs)).fst.length < xs.length + 1 :=
     by simp [length_halve_fst]; omega
    have : (halve₁ (x :: xs)).snd.length < xs.length + 1 :=
     by simp [length_halve_snd]; omega
    Tree.node (mkTree p.1) (mkTree p.2)
 termination_by xs => xs.length

def msort₀ [LE a] [DecidableRel (· ≤ · : a → a → Prop)]
 (xs : List a) : List a :=
 (flatten ∘ mkTree) xs

def msort₁ [LE a] [DecidableRel (· ≤ · : a → a → Prop)] : List a → List a
| []  => []
| x :: xs =>
  if h: xs.length = 0 then [x]
  else
    let p := halve₁ (x :: xs)
    have : (halve₁ (x :: xs)).fst.length < xs.length + 1 := by simp [length_halve_fst]; omega
    have : (halve₁ (x :: xs)).snd.length < xs.length + 1 := by simp [length_halve_snd]; omega
    merge (msort₁ p.1) (msort₁ p.2)

 termination_by xs => xs.length

/-
#eval msort₁ [5,3,4,2,1,1]
#eval msort₁ [1,2,3,4,5]
#eval msort₁ ['a','b','a']
-/

end S52

namespace S53 -- Heapsort

inductive Tree (α : Type): Type where
 | null : Tree α
 | node : α → Tree α → Tree α → Tree α
 deriving Repr, Inhabited

def flatten [LE a] [DecidableRel (α := a) (· ≤ ·)] : Tree a → List a
| Tree.null       => []
| Tree.node x u v => x :: S52.merge (flatten u) (flatten v)

end S53

end Chapter5

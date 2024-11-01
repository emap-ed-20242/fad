
namespace Chapter5

-- 5.1 Quicksort
namespace S51

inductive Tree a where
| null : Tree a
| node : (Tree a) → a → (Tree a) → Tree a

def mkTree : List Nat → Tree Nat
| [] => Tree.null
| x :: xs =>
  let p := xs.partition (λ y => decide (y < x))
  Tree.node (mkTree p.1) x (mkTree p.2)
 termination_by l => l.length
 decreasing_by
  all_goals simp [List.partition_eq_filter_filter,
   List.length_filter_le, Nat.lt_add_one_of_le]

def Tree.flatten : Tree a → List a
| null => []
| node l x r => l.flatten ++ [x] ++ r.flatten

def qsort₀ := Tree.flatten ∘ mkTree

#eval qsort₀ (List.iota 1000) |>.length


partial def qsort₁ [LT a] [DecidableRel (· < · : a → a → Prop)]
 : List a → List a
 | [] => []
 | (x :: xs) =>
  let p := xs.partition (· < x)
  (qsort₁ p.1) ++ [x] ++ (qsort₁ p.2)

#check qsort₁ [1,2,3,4,5]
#eval qsort₁ ['a','b','a']

structure Person where
  name : String
  age : Nat

instance : LT Person where
  lt p q := p.age < q.age

def people := [
  Person.mk "Alice" 23,
  Person.mk "Bob" 25,
  Person.mk "Eve" 22]

-- #eval qsort₁ people (how to prove decidability of Person.lt?)
end S51

-- 5.2 Mergesort
namespace S52

inductive Tree (α : Type) : Type where
 | null : Tree α
 | leaf : α → Tree α
 | node : Tree α → Tree α → Tree α
 deriving Repr, Inhabited

def merge [LE a] [DecidableRel (· ≤ · : a → a → Prop)]
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

#eval halve₀ [1,2,3,4,5,6,7,8,9,10]

def halve₁ : (xs : List a) → (List a × List a) :=
 let op x p := (p.2, x :: p.1)
 List.foldr op ([],[])

#eval halve₁ [1,2,3,4,5,6,7,8,9,10]
#eval halve₁ ([] : List Nat)

theorem halve_length_le_length : (halve₁ (x :: xs)).1.length ≤ xs.length := by
induction xs with
| nil => exact List.getElem?_eq_none_iff.mp rfl
| cons x xs ih =>
 unfold halve₁
 unfold halve₁ at ih
 rw [List.foldr]
 rw [List.foldr] at ih

def mkTree : (xs : List a) → Tree a
 | []  => Tree.null
 | [a] => Tree.leaf a
 | x::xs  =>
   let p := halve₁ (x::xs)
   Tree.node (mkTree p.1) (mkTree p.2)

   termination_by as => as.length
   decreasing_by
    simp [Nat.lt_succ_iff]
    exact halve_length_le_length

def msort₀ [LE a] [DecidableRel (· ≤ · : a → a → Prop)]
 (xs : List a) : List a :=
 (flatten ∘ mkTree) xs

def msort₁ [LE a] [DecidableRel (· ≤ · : a → a → Prop)]
 : List a → List a
 | []  => []
 | [x] => [x]
 | xs  =>
    let p := halve₁ xs
    merge (msort₁ p.1) (msort₁ p.2)
    termination_by as => as.length
    decreasing_by

#eval msort₁ [1,2,3,4,5]
#eval msort₁ ['a','b','a']


end S52

end Chapter5

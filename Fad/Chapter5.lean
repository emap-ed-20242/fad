
namespace Chapter5

-- 5.1 Quicksort

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

#eval qsort₀ (List.iota 1000)


partial def qsort₁ [LT a] [DecidableRel (· < · : a → a → Prop)] : List a → List a
| [] => []
| (x :: xs) =>
  let p := xs.partition (· < x)
  (qsort₁ p.1) ++ [x] ++ (qsort₁ p.2)

#eval qsort₁ (List.iota 1000)


end Chapter5

namespace Chapter5

/- 5.15:
  Show how to build a size-balanced tree, of the kind described in
  Heapsort, in linear time. Start with

  mktree [] = Null
  mktree (x : xs) = Node x (mktree (take m xs)) (mktree (drop m xs))
  where m = length xs div 2
-/

inductive Tree (a: Type) : Type
| null : Tree a
| node : a → (Tree a) → (Tree a) → Tree a

open Std.Format in
def Tree.toFormat [ToString α] : (t: Tree α) → Std.Format
| .null => Std.Format.text "."
| .node x t₁ t₂ =>
  bracket "(" (f!"{x}" ++
   line ++ nest 2 t₁.toFormat ++ line ++ nest 2 t₂.toFormat) ")"

instance [ToString a] : Repr (Tree a) where
 reprPrec e _ := Tree.toFormat e

--------------------------------------------------------------
def mkPair : Nat → (List a) → (Tree a × List a)
  | _, [] => (Tree.null, [])
  | n, x :: xs =>
    if h : n = 0 then (Tree.null, x :: xs) else
      let m := (n - 1) / 2
      have : m < n := by
        rw [show ¬n = 0 ↔ n > 0 by exact Nat.ne_zero_iff_zero_lt] at h
        rw [Nat.div_lt_iff_lt_mul Nat.zero_lt_two]

        calc
          n - 1 < n := Nat.sub_one_lt_of_lt h
          _ < n + n := Nat.lt_add_of_pos_right h
          _ = n * 2 := Eq.symm (Nat.mul_two n)
        
      let y := mkPair m xs
      let z := mkPair (n - 1 - m) y.snd
      have : (n - 1 - m) < n := by exact Nat.sub_one_sub_lt_of_lt this
      (Tree.node x y.fst z.fst, z.snd)
      termination_by n _ => n

def mkTree (xs : List a) : Tree a := (mkPair xs.length xs).1
--------------------------------------------------------------

#eval mkTree [1, 3, 2, 5, 5, 3, 4]

end Chapter5

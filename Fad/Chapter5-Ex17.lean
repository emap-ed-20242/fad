namespace Chapter5

/- 5.15:
  Show how to build a size-balanced tree, of the kind described in
  Heapsort, in linear time. Start with

  mktree [] = Null
  mktree (x : xs) = Node x (mktree (take m xs)) (mktree (drop m xs))
  where m = length xs div 2
-/

inductive Tree (a : Type) : Type
| null : Tree a
| node : a → (Tree a) → (Tree a) → Tree a

open Std.Format in
def Tree.toFormat [ToString α] : (t : Tree α) → Std.Format
| .null => Std.Format.text "."
| .node x t₁ t₂ =>
  bracket "(" (f!"{x}" ++
   line ++ nest 2 t₁.toFormat ++ line ++ nest 2 t₂.toFormat) ")"

instance [ToString a] : Repr (Tree a) where
 reprPrec e _ := Tree.toFormat e

--------------------------------------------------------------
def mkPair : Nat → (List a) → (Tree a × List a)
  | _, [] => (Tree.null, [])
  | 0, xs => (Tree.null, xs)
  | n, x :: xs =>
    let m := (n - 1) / 2
    let y := mkPair m xs
    let z := mkPair (n - 1 - m) y.2
    (Tree.node x y.1 z.1, z.2)

  termination_by n as => as
  decreasing_by -- ????????? PSigma.casesOn? instWellFoundedRelationOfSizeOf? invImage?
    simp [Nat.lt_add_one_iff, sizeOf]
    all_goals
    sorry

def mkTree (xs : List a) : Tree a := (mkPair xs.length xs).1
--------------------------------------------------------------

#eval mkTree [1, 3, 2, 5, 5, 3, 4]

end Chapter5

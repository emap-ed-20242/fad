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
deriving Repr

def mkTree : (List a) → Tree a
  | [] => Tree.null
  | x :: xs =>
    let m := xs.length / 2
    Tree.node x (mkTree (xs.take m)) (mkTree (xs.drop m))

  termination_by as => as.length
  decreasing_by
    all_goals
    simp [List.length_cons, Nat.lt_add_one_iff, Nat.min_le_right m xs.length]

#eval mkTree [1,4,2,3,3,2]

end Chapter5

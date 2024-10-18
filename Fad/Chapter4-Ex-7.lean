import Fad.Chapter4

namespace Chapter4

-- Exercise 4.7: To obtain a linear-time deﬁnition of ﬂatten we can use an accumulating parameter.
-- There is more than one way of doing so, but a simple method is to introduce ﬂatcat deﬁned by
--
--   ﬂatcat :: Tree a → \[a] → \[a]
--   ﬂatcat t xs = ﬂatten t ++ xs
--
-- We have ﬂatten t = ﬂatcat t [], so it remains to produce a recursive deﬁnition of ﬂatcat that
-- does not use ﬂatten or any ++ operations. Give details of the synthesis.

inductive Tree (a : Type) : Type where
| nil : Tree a
| node (l: Tree a) (x: a) (r: Tree a) : Tree a
deriving Repr

def flatten (t: Tree a): List a := match t with
| Tree.nil => []
| Tree.node l x r => (flatten l) ++ [x] ++ (flatten r)

def flatcat₁ (t: Tree a) (xs: List a): List a := flatten t ++ xs

----------------------------------------------------------------------------
def flatcat₂ (t: Tree a) (xs: List a): List a := match t, xs with
| Tree.nil, xs => xs
| (Tree.node l x r), xs => flatcat₂ l (x :: (flatcat₂ r xs))
----------------------------------------------------------------------------

-- Exemplo
def t1 := Tree.node (Tree.node (Tree.node Tree.nil 0 Tree.nil) 1 Tree.nil) 2 (Tree.node (Tree.node Tree.nil 3 Tree.nil) 4 (Tree.nil))
#eval flatcat₁ t1 [5, 6]
#eval flatcat₂ t1 [5, 6]

theorem flatcats_eq (t: Tree a) (xs: List a) : flatcat₁ t xs = flatcat₂ t xs := by
  induction t generalizing xs with
  | nil => exact rfl
  | node l x r ihl ihr =>
    simp [flatcat₁, flatten, flatcat₂, <-ihr, <-ihl]
  
end Chapter4


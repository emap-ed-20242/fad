
namespace Chapter3

open List (reverse tail cons)

-- 3.1 Symmetric lists

def snoc {a : Type u} (x : a) (xs : List a) : List a :=
  xs ++ [x]

def SymList (α : Type u) := (List α) × (List α)

def nilSL : SymList a := ([], [])

def fromSL (sl : SymList a) : List a :=
 sl.1 ++ sl.2.reverse

def snocSL : a → SymList a → SymList a
| z, ([],    ys) => (ys, [z])
| z, (b::bs, ys) => (b::bs, z :: ys)

def consSL : a → SymList a → SymList a
| z, (xs, []) => ([z], xs)
| z, (xs, ys) => (z :: xs, ys)

#eval fromSL $ consSL 4 $ consSL 3 $ consSL 2 $ consSL 1 nilSL

def lastSL : SymList a → Option a
| (xs, ys) => if ys.isEmpty then xs.head? else ys.head?

#eval fromSL (snocSL 1 (snocSL 2 (snocSL 3 ([], []))))

def _root_.List.splitAt (xs : List a) (n : Nat) : List a × List a :=
 (xs.take n, xs.drop n)

#eval [1, 2, 3, 4, 5].splitAt 2

def tailSL (sl : SymList a) : Option (SymList a) :=
 let (us, vs) := sl.2.splitAt (sl.2.length / 2)
 match sl with
 | ([],       []) => none
 | ([],  _ :: []) => some nilSL
 | (_ :: [],   _) => some (reverse vs, us)
 | (xs,       ys) => some (tail xs, ys)

#eval tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], []))))
#eval do let a ← tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], [])))); pure $ fromSL a

#check pure ∘ fromSL
#eval tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], [])))) >>= pure ∘ fromSL

-- Evidencias como argumentos

/- https://lean-lang.org/functional_programming_in_lean/props-proofs-indexing.html#evidence-as-arguments -/

#eval [].head (by simp)
#eval [1,2].head (by simp)

def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

#eval third [1, 2, 3, 4] (by decide)



end Chapter3

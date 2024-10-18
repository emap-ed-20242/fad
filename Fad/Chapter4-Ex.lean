import Fad.Chapter4

namespace Chapter4

/- complete here -/


/- 4.17 -/

section
open Chapter4.Tree2

abbrev Set (α : Type) : Type := Tree α

def pair  (f : α -> β) (p : α × α) : (β × β) := (f p.1, f p.2)

def split [LE α] [LT α] [DecidableRel (@LT.lt α _)] [DecidableRel (@LE.le α _)]
 (x : α) (t : Set α)
 : Set α × Set α :=
 pair (λ xs => mkTree xs) $ List.partition (· ≤ x) $ Tree.flatten t

#eval split 4 $ mkTree (List.iota 10)

end

end Chapter4

import Fad.Chapter4

namespace Chapter4

/- 4.2

smallest (a, b) returns the first x such that f(x) <= t, but f(x+1) > t.
That is, x is the point where the function f(x) crosses the threshold t.

But t = 1024 so...-/

#eval D1.smallest (fun x => dbg_trace "fun {x}"; x * x) 1024 (0, 1024)
#eval (fun x => dbg_trace "fun {x}"; x * x) 32
#eval (fun x => dbg_trace "fun {x}"; x * x) 33


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

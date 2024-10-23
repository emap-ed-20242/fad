
namespace Chapter3

open List (reverse tail cons)

-- 3.1 Symmetric lists

def _root_.List.single (xs : List α) : Bool := xs.length = 1

-- def _root_.List.splitAt (xs : List a) (n : Nat) : List a × List a :=
--  (xs.take n, xs.drop n)

/- motivação: algumas operações em listas encadeadas tem custo linear
   e outras constante. -/

def snoc {a : Type} (x : a) (xs : List a) : List a :=
  xs ++ [x]


namespace SL1

abbrev SymList (α : Type u) := (List α) × (List α)

#check ([],[])

def nilSL : SymList a := ([], [])

def fromSL (sl : SymList a) : List a :=
 sl.1 ++ sl.2.reverse

def snocSL : a → SymList a → SymList a
| z, ([], ys) => (ys, [z])
| z, (bs, ys) => (bs, z :: ys)

def consSL : a → SymList a → SymList a
| z, (xs, []) => ([z], xs)
| z, (xs, ys) => (z :: xs, ys)

def toSL : List a → SymList a
 | [] => nilSL
 | x :: xs => consSL x (toSL xs)

#eval fromSL $ consSL 4 $ consSL 3 $ consSL 2 $ consSL 1 nilSL
#eval toSL (List.iota 20)

def lastSL : SymList a → Option a
| (xs, ys) => if ys.isEmpty then xs.head? else ys.head?

#eval fromSL (snocSL 1 (snocSL 2 (snocSL 3 ([], []))))

def tailSL (sl : SymList a) : Option (SymList a) :=
 match sl with
 | ([],       []) => none
 | ([],  _ :: []) => some nilSL
 | (_ :: [],  ys) =>
   let (us, vs) := ys.splitAt (ys.length / 2)
   some (reverse vs, us)
 | (xs,       ys) => some (tail xs, ys)

#eval tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], []))))
#eval do
 let a ← tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], []))))
 pure $ fromSL a

#eval tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], [])))) >>= pure ∘ fromSL


end SL1

/-
 https://lean-lang.org/functional_programming_in_lean/props-proofs-indexing.html#evidence-as-arguments

 Uma segunda implementação onde o tipo carrega a prova das invariantes da
 estrutura.
-/

#check ([] : List Nat)
#eval ([] : List Nat).head?
#eval [1,2].head?

-- #eval [].head (by simp)
#eval [1,2].head (by simp)

def test (xs : List α) (ok : xs.length > 2) : α := xs[2]
#eval test [1, 2, 3, 4] (by simp)


namespace SL2

structure SymList (α : Type) where
  lhs : List α
  rhs : List α
  ok : (lhs.isEmpty → rhs.isEmpty ∨ rhs.length = 1) ∧
       (rhs.isEmpty → lhs.isEmpty ∨ lhs.length = 1)
 deriving Repr

 def P (sl : SymList a) : Prop :=
 sl.1.length > sl.2.length

def sl_ex₁ := { lhs := [1], rhs := [4,5,6], ok := (by simp) : SymList Nat }
def sl_ex₂ := { lhs := [1,2,3,4], rhs := [5,6,7], ok := (by simp) : SymList Nat}
#eval (sl_ex₁.1.length > sl_ex₁.2.length) -- False
#eval (sl_ex₂.1.length > sl_ex₂.2.length) -- True

-- Not always true that lhs.length > rhs.length given our SymList definition
example : ∀ sl : SymList Nat, P sl := by
  intro sl
  cases sl with
  | mk as bs h => sorry

-- Counter-Example
example : ∃ sl : SymList Nat, ¬P sl := by
  exists SymList.mk [1, 2] [3, 4, 5] (by simp)
  simp [P]

#eval SymList.mk [1,2,3] [4,5,6] (by simp)
#eval { lhs := [], rhs := [6], ok := (by simp) : SymList Nat }

def fromSL (sl : SymList a) : List a :=
 sl.lhs ++ sl.rhs.reverse

def nilSL : SymList a := SymList.mk [] [] (by simp)

def snocSL : a → SymList a → SymList a
| z, SymList.mk [] bs _ => SymList.mk bs [z] (by simp)
| z, SymList.mk (a::as) bs _ => SymList.mk (a::as) (z :: bs) (by simp)

def consSL : a → SymList a → SymList a
| z, SymList.mk xs [] _ => SymList.mk [z] xs (by simp)
| z, SymList.mk xs (y::ys) _ => SymList.mk (z :: xs) (y::ys) (by simp)

def toSL : List a → SymList a
 | [] => nilSL
 | x :: xs => consSL x (toSL xs)

def headSL : SymList a → Option a
 | SymList.mk []     []     _ => none
 | SymList.mk []     (y::_) _ => some y
 | SymList.mk (x::_) _      _ => some x

#eval headSL <| toSL <| List.iota 20
#eval headSL <| (nilSL : SymList Nat)

def lastSL : SymList a → Option a
| SymList.mk xs ys _ => if ys.isEmpty then xs.head? else ys.head?

#eval lastSL <| toSL <| List.range 20
#eval lastSL <| (nilSL : SymList Nat)

def nullSL (sl : SymList a) : Bool :=
  sl.lhs.isEmpty ∧ sl.rhs.isEmpty

#eval nullSL <| toSL <| List.iota 20
#eval nullSL <| (nilSL : SymList Nat)

def singleSL (sl : SymList a): Bool :=
  (List.single sl.lhs ∧ sl.rhs.isEmpty) ∨
  (List.single sl.rhs ∧ sl.lhs.isEmpty)

#eval singleSL <| toSL <| List.iota 20
#eval singleSL <| (nilSL : SymList Nat)
#eval singleSL <| SymList.mk [42] [] (by simp)

def lengthSL (sl : SymList a) : Nat :=
  sl.lhs.length + sl.rhs.length

#eval lengthSL <| toSL <| List.range 42
#eval lengthSL <| (nilSL : SymList Nat)
#eval lengthSL <| SymList.mk [] [42] (by simp)

/--- FIXME: Finish definitions; proof is missing for
cases 3 and 4 on both tailSL and initSL.

def tailSL (xs : SymList a) : Option (SymList a) :=
  let (us, vs) := xs.rhs.splitAt (xs.rhs.length / 2)
  match xs.lhs, xs.rhs with
  | []   , [] => none
  | []   , _  => some nilSL
  | _::[], _  => some (SymList.mk (reverse vs) us (by sorry))
  | _    , _  => some (SymList.mk (tail xs.lhs) xs.rhs (by sorry))

def initSL (xs : SymList a) : Option (SymList a) :=
  let (us, vs) := xs.rhs.splitAt (xs.rhs.length / 2)
  match xs.lhs, xs.rhs with
  | [],      [] => none
  | _ ,      [] => some nilSL
  | _ , _ :: [] => some (SymList.mk us (reverse vs) (by sorry))
  | _ , _       => some (SymList.mk xs.lhs (tail xs.rhs) (by sorry))-/

-- Alternate definition for tailSL and initSL, not sure if they're right, but I couldn't prove the ones above.
def tailSL (xs : SymList a) : Option (SymList a) :=
  let (us, vs) := xs.rhs.splitAt (xs.rhs.length / 2)
  match xs.lhs, xs.rhs with
  | []   , [] => none
  | []   , _  => some nilSL
  | _::[], _  => some (toSL (reverse vs ++ us))
  | _    , _  => some (toSL (tail xs.lhs ++ xs.rhs))

#eval tailSL { lhs := (List.iota 10), rhs := (List.range 10), ok := (by simp) }
#eval tailSL <| toSL <| List.iota 20
#eval tailSL { lhs := [1], rhs := [2, 3], ok := (by simp) }

def initSL (xs : SymList a) : Option (SymList a) :=
  let (us, vs) := xs.rhs.splitAt (xs.rhs.length / 2)
  match xs.lhs, xs.rhs with
  | [],      [] => none
  | _ ,      [] => some nilSL
  | _ , _ :: [] => some (toSL (us ++ reverse vs))
  | _ , _       => some (toSL (xs.lhs ++ tail xs.rhs))

#eval initSL <| toSL <| List.iota 20
#eval initSL <| SymList.mk [1] [2, 3] (by simp)
#eval initSL { lhs := (List.iota 10), rhs := (List.range 10), ok := (by simp) }

-- FIXME: Termination proof is missing
set_option trace.Meta.Tactic.simp.rewrite true in
def dropWhileSL (p : a → Bool) (sl : SymList a) : SymList a :=
  match sl with
  | SymList.mk [] [] _ => nilSL
  | SymList.mk xs ys _ =>
    match headSL sl with
    | none => nilSL
    | some hsl =>
      if p hsl then
        match tailSL sl with
        | none     => nilSL
        | some tsl => dropWhileSL p tsl
      else sl
 termination_by
  lengthSL sl
 decreasing_by
  simp [lengthSL, tailSL]
  sorry -- couldn't finish proof

-- FIXME: Termination proof is missing
def initsSL (sl : SymList a) : SymList (SymList a) :=
  if   nullSL sl
  then snocSL sl nilSL
  else
    match initSL sl with
    | none     => nilSL
    | some isl => snocSL sl (initsSL isl)
 termination_by
    lengthSL sl
 decreasing_by
  simp [lengthSL, initSL]
  sorry -- couldn't finish proof


example (us vs : List Nat)
 : [] ++ reverse (us ++ vs) = reverse vs ++ reverse us := by simp


example {a : Type} (x : a) : cons x ∘ fromSL = fromSL ∘ consSL x := by
 funext s
 cases s with
 | mk as bs h =>
   induction bs with
   | nil =>
     simp [consSL, fromSL]
     simp at h
     apply Or.elim h
     intro h1 ; rw [h1]; simp
     intro h1
     induction as with
     | nil => simp
     | cons z zs _ =>
       simp at h1
       rw [h1]; simp
   | cons z zs _ => simp [consSL, fromSL]


end SL2


-- 3.2 Random-access lists

def fetch : Nat → List a → Option a
 | _, [] => none
 | k, x::xs => if k = 0 then x else fetch (k - 1) xs

#eval [1,2,3,4].get? 2
#eval fetch 2 [1,2,3,4]


inductive Tree (α : Type) : Type where
 | leaf (n : α) : Tree α
 | node (n : Nat) (t₁ : Tree α) (t₂ : Tree α) : Tree α
 deriving Repr

def Tree.toString [ToString α] : Tree α → String
 | leaf x => s!"leaf {x}"
 | node n t₁ t₂ => s!"node {n} ({t₁.toString}) ({t₂.toString})"

instance [ToString α] : ToString (Tree α) where
  toString := Tree.toString

def Tree.size : Tree a → Nat
 | leaf _ => 1
 | node n _ _ => n

def Tree.height : Tree α → Nat
 | leaf _ => 1
 | node _ t₁ t₂ => 1 + max t₁.height t₂.height

def Tree.mk (t₁ t₂ : Tree a) : Tree a :=
 node (t₁.size + t₂.size) t₁ t₂

open Tree

#eval mk (mk (leaf 'a') (leaf 'b')) (mk (leaf 'c') (leaf 'd'))

inductive Digit (a : Type) : Type where
 | zero : Digit a
 | one (t : Tree a) : Digit a
 deriving Repr

def Digit.toString [ToString α] : Digit α → String
  | zero => "zero"
  | one t => s!"one ({t.toString})"

instance [ToString α] : ToString (Digit α) where
  toString := Digit.toString

open Digit

-- works with def too
abbrev RAList (a : Type) : Type := List (Digit a)

#check ([Digit.zero, Digit.zero] : RAList Nat)

def concat1 {a : Type} : List (List a) → List a :=
 List.foldr List.append []

def concatMap (f : a → List b) : List a → List b :=
 concat1 ∘ (List.map f)


def fromT : Tree a → List a
 | (leaf x) => [x]
 | (node _ t₁ t₂) => fromT t₁ ++ fromT t₂

def fromRA : RAList a → List a :=
  concatMap frm
 where
  frm : Digit a → List a
   | Digit.zero => []
   | Digit.one t => fromT t

#eval fromRA [zero,
        one (mk (leaf 'a') (leaf 'b')),
        one (mk (mk (leaf 'c') (leaf 'd'))
                (mk (leaf 'e') (leaf 'f')))]


def fetchT [ToString a] (n : Nat) (t : Tree a) : Option a :=
 match n, t with
 | 0, leaf x => x
 | k, (node n t₁ t₂) =>
   let m := n / 2
   if k < m then fetchT k t₁ else fetchT (k - m) t₂
 | _, leaf _ => none

def fetchRA [ToString a] (n : Nat) (ra : RAList a) : Option a :=
 match n, ra with
 | _, [] => none
 | k, (zero :: xs) => fetchRA k xs
 | k, (one t :: xs) =>
   if k < size t then fetchT k t else fetchRA (k - size t) xs

#eval fetchRA 10 [zero,
        one (mk (leaf 'a') (leaf 'b')),
        one (mk (mk (leaf 'c') (leaf 'd'))
                (mk (leaf 'e') (leaf 'f')))]


def nilRA {a : Type} : RAList a := []

def consRA (x : a) (xs : RAList a) : RAList a :=
 consT (Tree.leaf x) xs
where
 consT : Tree a → RAList a → RAList a
 | t1, [] => [Digit.one t1]
 | t1, Digit.zero :: xs => Digit.one t1 :: xs
 | t1, Digit.one t2 :: xs => Digit.zero :: consT (Tree.mk t1 t2) xs

-- 3.3 Arrays

def listArray (xs : List α) : Array α :=
 xs.toArray


end Chapter3

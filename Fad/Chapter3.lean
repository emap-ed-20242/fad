
namespace Chapter3

open List (reverse tail cons)

-- 3.1 Symmetric lists

def _root_.List.single (xs : List α) : Bool := xs.length = 1

/- motivação: algumas operações em listas encadeadas tem custo linear
   e outras constante. -/

def snoc {a : Type} (x : a) (xs : List a) : List a :=
  xs ++ [x]


namespace SL1

abbrev SymList (α : Type u) := (List α) × (List α)

-- #check ([],[])

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

-- #eval fromSL $ consSL 4 $ consSL 3 $ consSL 2 $ consSL 1 nilSL
-- #eval toSL (List.iota 20)

def lastSL : SymList a → Option a
| (xs, ys) => if ys.isEmpty then xs.head? else ys.head?

-- #eval snocSL 20 (snocSL 10 (snocSL 1 (snocSL 2 (snocSL 3 ([], [])))))

def tailSL (sl : SymList a) : Option (SymList a) :=
 match sl with
 | ([],       []) => none
 | ([],  _ :: []) => some nilSL
 | (_ :: [],  ys) =>
   let (us, vs) := ys.splitAt (ys.length / 2)
   some (reverse vs, us)
 | (xs,       ys) => some (tail xs, ys)

/- 
#eval tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], []))))
#eval do
 let a ← tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], []))))
 pure $ fromSL a

#eval tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], [])))) >>= pure ∘ fromSL
-/

end SL1

/-
 https://lean-lang.org/functional_programming_in_lean/props-proofs-indexing.html#evidence-as-arguments

 Uma segunda implementação onde o tipo carrega a prova das invariantes da
 estrutura.
-/

/-
#check ([] : List Nat)
#eval ([] : List Nat).head?
#eval [1,2].head?

#eval [].head (by simp)
#eval [1,2].head (by simp)

def test (xs : List α) (ok : xs.length > 2) : α := xs[2]
#eval test [1, 2, 3, 4] (by simp)
-/


namespace SL2

-- it may simplify the proofs
structure SymList' (α : Type) where
  lhs : List α
  rhs : List α
  ok : (lhs.length = 0 → rhs.length ≤ 1) ∧
       (rhs.length = 0 → lhs.length ≤ 1)
 deriving Repr

structure SymList (α : Type) where
  lhs : List α
  rhs : List α
  ok : (lhs.isEmpty → rhs.isEmpty ∨ rhs.length = 1) ∧
       (rhs.isEmpty → lhs.isEmpty ∨ lhs.length = 1)
 deriving Repr

def nilSL : SymList a := SymList.mk [] [] (by simp)

instance : Inhabited (SymList α) where
  default := nilSL

def fromSL (sl : SymList a) : List a :=
 sl.lhs ++ sl.rhs.reverse

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
 | ⟨[], [], _⟩     => none
 | ⟨[], y :: _, _⟩ => some y
 | ⟨x::_, _, _⟩    => some x

def lastSL : SymList a → Option a
| SymList.mk xs ys _ => if ys.isEmpty then xs.head? else ys.head?

def nullSL (sl : SymList a) : Bool :=
  sl.lhs.isEmpty ∧ sl.rhs.isEmpty

def singleSL (sl : SymList a): Bool :=
  (List.single sl.lhs ∧ sl.rhs.isEmpty) ∨
  (List.single sl.rhs ∧ sl.lhs.isEmpty)

def lengthSL (sl : SymList a) : Nat :=
  sl.lhs.length + sl.rhs.length


/- subtipos -/
def p (h : List Nat) : Prop := h.length = 3

def test₁ := (@Subtype.mk _ p [1,2,3] (by simp [p]))
def test₂ := (Subtype.mk [1,2,3] (by rfl : p [1,2,3]) )

/-
#check p [1,2,3]
#eval test₁.val
#check test₁.property
#check List.splitInTwo test₁
#check List.splitInTwo (Subtype.mk [1,2,3,4] (by rfl))
-/

def splitInTwoSL (xs : List a) : SymList a :=
  let p := List.splitInTwo (Subtype.mk xs (by rfl))
  SymList.mk p.1 p.2.val.reverse (by
    have ⟨⟨as, aok⟩, ⟨bs, bok⟩⟩ := p
    simp [aok, bok]
    apply And.intro <;> (intro h; simp [h] at bok aok)
    if h2: bs.length = 0 then simp at h2; simp [h2] else omega
    if h2: as.length = 0 then simp at h2; simp [h2] else omega)

def tailSL {a : Type} (as : SymList a) : SymList a :=
  match as with
  | ⟨xs, ys, ok⟩ =>
    if h : xs.isEmpty then
      match ys with
      | [] => nilSL
      |  _ => nilSL
    else
      if h2 : xs.length = 1 then splitInTwoSL ys.reverse
      else (SymList.mk xs.tail ys (by
        simp [← not_congr List.length_eq_zero] at h
        apply And.intro <;> (intro h3; have k :: (l :: ms) := xs)
        repeat simp [ok] at *))

def initSL {a : Type} : (sl : SymList a) → SymList a
| ⟨xs, ys, ok⟩ =>
  if h : ys.isEmpty then
    match xs with
    | [] => nilSL
    | _  => nilSL
  else
    if h2 : ys.length = 1 then splitInTwoSL xs
    else (SymList.mk xs ys.tail (by
      simp [← not_congr List.length_eq_zero] at h
      apply And.intro
      all_goals
       intro h3
       simp [h3] at ok
       have a :: [] := ys
       simp at *))

/-
#eval fromSL $ SymList.mk [1] [3,2] (by simp)
#eval fromSL $ tailSL $ SymList.mk [1] [3,2] (by simp)
#eval fromSL $ initSL $ SymList.mk [1] [3,2] (by simp)

#check (fromSL ∘ tailSL : SymList Nat → List Nat)
#check (tail ∘ fromSL : SymList Nat → List Nat)
-/

example : ∀ (as : SymList α), fromSL (tailSL as) = tail (fromSL as) := by
  intro sl
  have ⟨xs, ys, ok⟩ := sl
  cases xs with
  | nil =>
    induction ys with
    | nil => simp [tailSL, fromSL, nilSL]
    | cons b bs ih =>
      simp [fromSL, tailSL, nilSL]
      simp [ok] at *
      rw [ok]
      rw [List.reverse_nil, List.nil_append, List.tail]
  | cons a as =>
    induction ys with
    | nil =>
      by_cases h : as = [] <;> simp [h, fromSL, tailSL, splitInTwoSL]
    | cons b bs ih =>
      by_cases h: as = []
      . simp [h, List.tail, fromSL] at ih
        simp [h, fromSL, tailSL]
        simp [splitInTwoSL]
      . simp [tailSL, h, fromSL]


theorem length_sl_eq_length (xs : List a)
 : lengthSL (splitInTwoSL xs) = List.length xs := by
  simp [splitInTwoSL, lengthSL]
  omega

theorem length_init_lt_length (sl : SymList a) (h : sl ≠ nilSL)
 : lengthSL sl > lengthSL (initSL sl) := by
  have ⟨lsl, rsl, _⟩ := sl
  unfold lengthSL initSL
  simp
  simp [nilSL] at h
  by_cases hr: rsl = [] <;> simp [hr]
  by_cases hl: lsl = [] <;> simp [hl]
  have := h hl
  contradiction
  simp [nilSL]
  simp [<-List.length_eq_zero] at hl
  omega
  by_cases hr2: rsl.length = 1 <;> simp [hr2]
  rw [<-lengthSL]
  simp [length_sl_eq_length]
  refine @Nat.sub_one_lt_of_lt rsl.length 0 (by
    simp [<-List.length_eq_zero] at hr
    omega
  )

theorem length_tail_lt_length (sl : SymList a) (h : sl ≠ nilSL)
 : lengthSL sl > lengthSL (tailSL sl) := by
  have ⟨lsl, rsl, _⟩ := sl
  unfold lengthSL tailSL
  simp
  simp [nilSL] at h
  by_cases hr: rsl = [] <;> (simp [hr]; by_cases hl: lsl = [] <;> simp [hl])
  have := h hl
  contradiction
  by_cases hl2: lsl.length = 1 <;> simp [hl2]
  simp [splitInTwoSL]
  refine @Nat.sub_one_lt_of_lt lsl.length 0 (by
    have : lsl.length ≠ 0 := by simp [hl]
    omega
  )
  exact List.length_lt_of_drop_ne_nil (h hl)
  by_cases hl2: lsl.length = 1 <;> simp [hl2]
  rw [<-lengthSL]
  rw [length_sl_eq_length]
  simp
  refine @Nat.sub_one_lt_of_lt lsl.length 0 (by
    have : lsl.length ≠ 0 := by simp [hl]
    omega
  )

def initsSL (sl : SymList a) : SymList (SymList a) :=
  if h: nullSL sl
  then snocSL sl nilSL
  else
    have : lengthSL (initSL sl) < lengthSL sl := length_init_lt_length sl (by
      have ⟨lsl, rsl, _⟩ := sl
      simp [nullSL] at h
      simp [nilSL]
      exact h
    )
    snocSL sl (initsSL (initSL sl))

  termination_by lengthSL sl

theorem headSL_none_iff_nilSL: headSL sl = none ↔ sl = nilSL := by
  apply Iff.intro <;> intro h
  unfold headSL at h
  split at h
  unfold nilSL
  exact rfl
  repeat simp [eq_comm, <-Option.isNone_iff_eq_none] at h

  rw [h]
  unfold headSL nilSL
  simp

theorem lengthSL_zero_iff_nilSL: lengthSL sl = 0 ↔ sl = nilSL := by
  apply Iff.intro <;> intro h
  rw [lengthSL] at h
  rw [Nat.add_eq_zero_iff] at h
  repeat rw [List.length_eq_zero] at h
  unfold nilSL
  have ⟨h1, h2⟩ := h
  have ⟨lhs, rhs, ok⟩ := sl
  simp at h1 h2
  simp [h1, h2]

  rw [h]
  unfold nilSL lengthSL
  simp

def dropWhileSL (p : a → Bool) (sl : SymList a) : SymList a :=
  if sl.lhs.isEmpty ∧ sl.rhs.isEmpty then nilSL else
    match h: headSL sl with
    | none => nilSL
    | some hsl =>
      if p hsl then
        let tl := tailSL sl
        have : lengthSL (tailSL sl) < lengthSL sl := length_tail_lt_length sl (by
          if h2: sl = nilSL then
            rw [<-headSL_none_iff_nilSL] at h2
            rw [h2] at h
            contradiction
          else
            exact h2
        )
        dropWhileSL p tl
      else sl

    termination_by lengthSL sl

example {a : Type} (x : a) : cons x ∘ fromSL = fromSL ∘ consSL x := by
 funext s
 cases s with
 | mk as bs h =>
   cases bs with
   | nil =>
     simp [consSL, fromSL]
     simp at h
     apply Or.elim h
     intro h1 ; rw [h1]; simp
     intro h1
     cases as with
     | nil => simp
     | cons z zs =>
       simp at h1
       rw [h1]; simp
   | cons z zs => simp [consSL, fromSL]


example {a : Type} (x : a) : snoc x ∘ fromSL = fromSL ∘ snocSL x := by
 sorry


end SL2


-- 3.2 Random-access lists

def fetch : Nat → List a → Option a
 | _, [] => none
 | k, x::xs => if k = 0 then x else fetch (k - 1) xs

/-
#eval [1,2,3,4].get? 2
#eval fetch 2 [1,2,3,4]
-/

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

-- #eval mk (mk (leaf 'a') (leaf 'b')) (mk (leaf 'c') (leaf 'd'))

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

-- #check ([Digit.zero, Digit.zero] : RAList Nat)

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

/-
#eval fromRA [zero,
        one (mk (leaf 'a') (leaf 'b')),
        one (mk (mk (leaf 'c') (leaf 'd'))
                (mk (leaf 'e') (leaf 'f')))]
-/

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

/-
#eval fetchRA 10 [zero,
        one (mk (leaf 'a') (leaf 'b')),
        one (mk (mk (leaf 'c') (leaf 'd'))
                (mk (leaf 'e') (leaf 'f')))]
-/

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

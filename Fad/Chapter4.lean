
import Fad.Chapter1

namespace Chapter4

-- 4.1 A one-dimensional search problem

namespace D1

def search₀ (f : Nat → Nat) (t : Nat) : List Nat :=
 List.foldl (fun xs x => if t = f x then x :: xs else xs) []
  (List.range <| t + 1)

def search₁ (f : Nat → Nat) (t : Nat) : List Nat :=
  seek (0, t)
 where
  acc xs x := if t = f x then x :: xs else xs
  seek : (Nat × Nat) → List Nat
  | (a, b) => List.foldl acc [] <| List.range' a (b - a + 1)


def search₂ (f : Nat → Nat) (t : Nat) : List Nat :=
 let rec seek (a b : Nat) : List Nat :=
  let m := (a + b) / 2
   if h₁ : a > b then  []
   else if h₂ : t < f m then
    have : (a + b) / 2 - 1 - a < b - a := by
     rw [Nat.not_gt_eq] at h₁
     sorry
    seek a (m - 1)
   else if h₃ : t = f m then [m]
   else
    have : b - ((a + b) / 2 + 1) < b - a := by
     sorry
    seek (m + 1) b
 termination_by (b - a)
 seek 0 t


def bound (f : Nat → Nat) (t : Nat) : (Int × Nat) :=
  if t ≤ f 0 then (-1, 0) else (b / 2, b)
 where
  b := Chapter1.until' done (· * 2) 1
  done b := t ≤ f b

partial def smallest (f : Nat → Nat) (t : Nat) : (Int × Nat) → Nat
| (a, b) =>
  let m := (a + b) / 2
  if a + 1 = b then b
  else
   if t ≤ f m.toNat
   then
    smallest f t (a, m.toNat)
   else
    smallest f t (m, b)

partial def search₃ (f : Nat → Nat) (t : Nat) : List Nat :=
  if f x = t then [x] else []
 where
  x := smallest f t (bound f t)

#eval bound (fun x => dbg_trace "fun {x}"; x * x) 1024

#eval search₁ (fun x => dbg_trace "fun {x}"; x * x) 1024
-- #eval search₂ (fun x => dbg_trace "fun {x}"; x * x) 2025
#eval search₃ (fun x => dbg_trace "fun {x}"; x * x) 2025

end D1


-- 4.2 A two-dimensional search problem

namespace D2

def search₀ (f : (Nat × Nat) → Nat) (t : Nat) : List (Nat × Nat) :=
 ps.filter (λ p => t = f p)
 where
  as := (List.range $ t + 1)
  ps := Chapter1.concatMap (λ x => as.map (λ y => (x, y))) as

#eval search₀ (λ p => dbg_trace "fun {p}"; p.1 + p.2) 5

/- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20proof.20termination -/

def search₁ (f : Nat × Nat → Nat) (t : Nat) : List (Nat × Nat) :=
  searchIn 0 t []
where
  searchIn (x y : Nat) (sofar : List (Nat × Nat)) : List (Nat × Nat) :=
    let z := f (x, y)
    if x > t then sofar
    else if z < t then
      searchIn (x + 1) y sofar
    else if z = t then
      match y with
      | 0 => (x,y) :: sofar
      | y' + 1 => searchIn (x + 1) y ((x, y) :: sofar)
    else
      match y with
      | 0 => sofar
      | y + 1 => searchIn x y sofar
  termination_by (t + 1 - x, y)

#eval search₁ (λ (x, y) => dbg_trace "fun {x} {y}"; x + y) 5
#eval search₁ (λ (x, y) => dbg_trace "fun {x} {y}"; x^2 + 3^y) 12
#eval search₁ (λ (x, y) => x^2 + 3^y) 2223
#eval search₁ (λ (x, y) => x^2 + 3^y) 20259


partial def helper (t : Nat) (f : Nat × Nat → Nat)
 : (Nat × Nat) → (Nat × Nat) → List (Nat × Nat)
 | (x₁, y₁), (x₂, y₂) =>
  let c := (x₁ + x₂) / 2
  let r := (y₁ + y₂) / 2
  let x := D1.smallest (λ x => f (x,r)) t (x₁ - 1, x₂)
  let y := D1.smallest (λ y => f (c,y)) t (y₂ - 1, y₁)
  if x₂ < x₁ ∨ y₁ < y₂ then
   []
  else
   if y₁ - y₂ ≤ x₂ - x₁ then
    let z := f (x,r)
    if z < t then
     helper t f (x₁, y₁) (x₂, r + 1)
    else if z = t then
     (x, r) :: helper t f (x₁, y₁) (x - 1, r + 1) ++ helper t f (x + 1, r - 1) (x₂, y₂)
    else
     helper t f  (x₁, y₁) (x - 1, r + 1) ++ helper t f (x, r - 1) (x₂, y₂)
   else
    let z := f (c, y)
    if z < t then
     helper t f (c + 1, y₁) (x₂, y₂)
    else if z = t then
     (c, y) :: helper t f (x₁, y₁) (c - 1, y + 1) ++ helper t f (c + 1, y - 1) (x₂, y₂)
    else
     helper t f (x₁, y₁) (c - 1, y) ++ helper t f (c + 1, y - 1) (x₂, y₂)

partial def search₂ (f : Nat × Nat → Nat) (t : Nat) : List (Nat × Nat) :=
 let p := D1.smallest (λ y => f (0, y)) t (-1, t)
 let q := D1.smallest (λ x => f (x, 0)) t (-1, t)
 helper t f (0, p) (q, 0)


-- BUG #eval helper 12 (λ (x, y) => x^2 + 3^y) (0, 12) (12,0)


/- https://kmill.github.io/informalization/ucsc_cse_talk.pdf -/

def scale (a : Array Int) (c : Int) : Array Int := Id.run do
  let mut b : Array Int := #[]
  for h: i in [0:a.size] do
   b := b.push (c * a[i])
  return b

#eval scale #[1,2,3,4] 4
#eval for i in [0:12] do println! i

def myhead₁ (xs : List a) (h : xs.length ≠ 0) : a :=
 match xs with
 | [] => absurd rfl h
 | x :: _ => x

def myhead₂ (xs : List a) (h : xs.length ≠ 0) : a :=
 match xs, h with
 | x :: _, _ => x

end D2


-- 4.3 Binary search trees

namespace Tree1

inductive Tree (α : Type) : Type
| null : Tree α
| node : (Tree α) → α → (Tree α) → Tree α
deriving Inhabited

open Std.Format in

def Tree.toFormat [ToString α] : (t : Tree α) → Std.Format
| .null => Std.Format.text "."
| .node t₁ x t₂ =>
  bracket "(" (f!"{x}" ++
   line ++ nest 2 t₁.toFormat ++ line ++ nest 2 t₂.toFormat) ")"

instance [ToString a] : Repr (Tree a) where
 reprPrec e _ := Tree.toFormat e

def Tree.size : Tree a → Nat
| null => 0
| node t₁ _ t₂ => 1 + t₁.size + t₂.size

def Tree.flatten : Tree a → List a
| null => []
| node l x r => l.flatten ++ [x] ++ r.flatten


/- failed to synthesize decidable
def search {a b : Type} [LT b] (f : a → b) : b → Tree a → Option a
| _, Tree.null => none
| k, Tree.node l x r =>
  if f x < k then
   search f k r
  else
   if f x = k then
    some x
   else
    search f k l
-/

def search (f : Nat → Nat) : Nat → Tree Nat → Option Nat
| _, Tree.null => none
| k, Tree.node l x r =>
  if f x < k then
   search f k r
  else
   if f x = k then
    some x
   else
    search f k l

def Tree.height : Tree a → Nat
| null => 0
| node l _ r => 1 + (max l.height r.height)


def mkTree : List Nat → Tree Nat
| [] => Tree.null
| x :: xs =>
  let p := xs.partition (· < x)
  Tree.node (mkTree p.1) x (mkTree p.2)
 termination_by l => l.length
 decreasing_by
  all_goals
   simp [List.partition_eq_filter_filter,
         List.length_filter_le, Nat.lt_add_one_of_le]


#eval mkTree (List.iota 20)

end Tree1

namespace Tree2

inductive Tree (α : Type) : Type
| null : Tree α
| node : Nat → (Tree α) → α → (Tree α) → Tree α

open Std.Format in

def Tree.toFormat [ToString α] : (t : Tree α) → Std.Format
| .null => Std.Format.text "."
| .node _ t₁ x t₂ =>
  bracket "(" (f!"{x}" ++
   line ++ nest 2 t₁.toFormat ++ line ++ nest 2 t₂.toFormat) ")"

instance [ToString a] : Repr (Tree a) where
 reprPrec e _ := Tree.toFormat e

def Tree.height : (a : Tree α) -> Nat
 | Tree.null => 0
 | Tree.node x _ _ _ => x

def Tree.flatten : Tree a → List a
| null => []
| node _ l x r => l.flatten ++ [x] ++ r.flatten

def node (l : Tree α) (x : α) (r : Tree α): Tree α :=
  Tree.node h l x r
 where h := 1 + (max l.height r.height)


def bias : Tree α → Int
| .null => 0
| .node _ l _ r => l.height - r.height

def rotr : Tree α → Tree α
| .null => .null
| .node _ (.node _ ll y rl) x r => node ll y (node rl x r)
| .node _ .null _ _ => .null

def rotl : Tree α → Tree α
| .null => .null
| .node _ ll y (.node _ lrl z rrl) => node (node ll y lrl) z rrl
| .node _ _ _ .null => .null


def balance (t1 : Tree α)  (x : α)  (t2 : Tree α) : Tree α :=
if Int.natAbs (h1 - h2) ≤ 1 then
  node t1 x t2
else if h1 == h2 + 2 then
 rotateR t1 x t2
else
 rotateL t1 x t2
where
  h1 := t1.height
  h2 := t2.height
  rotateR t1 x t2 :=
   if 0 <= bias t1 then
    rotr (node t1 x t2)
   else rotr (node (rotl t1) x t2)
  rotateL t1 x t2 :=
   if bias t2 <= 0 then
    rotl (node t1 x t2)
   else rotl (node t1 x (rotr t2))

def insert {α : Type} [LT α] [DecidableRel (@LT.lt α _)] : (x : α) -> Tree α -> Tree α
| x, .null => node .null x .null
| x, .node h l y r =>
  if x < y then balance (insert x l) y r else
  if x > y then balance l y (insert x r) else .node h l y r

def mkTree [LT α] [DecidableRel (@LT.lt α _)]
 : (xs : List α) → Tree α :=
 Chapter1.foldr insert (.null : Tree α)

#eval mkTree (List.iota 20)

end Tree2

end Chapter4

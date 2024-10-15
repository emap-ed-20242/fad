
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


partial def search₂ (f : Nat → Nat) (t : Nat) : List Nat :=
 let rec seek (a b : Nat) : List Nat :=
  let m := (a + b) / 2
   if a > b then  []
   else if t < f m then seek a (m - 1)
   else if t = f m then [m]
   else seek (m + 1) b
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
#eval search₃ (fun x => dbg_trace "fun {x}"; x * x) 1024

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

inductive Tree (α : Type) : Type
| null : Tree α
| node : (Tree α) → α → (Tree α) → Tree α
deriving Repr

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
 all_goals simp
  [p, List.partition_eq_filter_filter,
   List.length_filter_le, Nat.lt_add_one_of_le]

#eval mkTree [1,2,3,4,5,6]

end Chapter4

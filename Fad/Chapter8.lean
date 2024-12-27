import Fad.Chapter1
import Fad.Chapter5
import Fad.Chapter7

namespace Chapter8

/- 8.1 Minimum-height trees -/

open Chapter5.S52 (halve₁ length_halve_fst length_halve_snd pairWith)
open Chapter1 (wrap unwrap single until' concatMap)
open Chapter7 (minWith)

inductive Tree (α : Type) : Type where
 | leaf : α → Tree α
 | node : Tree α → Tree α → Tree α
 deriving Repr, Inhabited


def Tree.size {α : Type} : Tree α → Nat
 | Tree.leaf _ => 1
 | Tree.node t₁ t₂ => t₁.size + t₂.size


def Tree.height {α : Type} : Tree α → Nat
 | Tree.leaf _ => 0
 | Tree.node t₁ t₂ => Nat.max t₁.height t₂.height + 1


def Tree.fringe {α : Type} : Tree α → List α
 | Tree.leaf x => [x]
 | Tree.node t₁ t₂ => t₁.fringe ++ t₂.fringe


def mkTree {a : Type} [Inhabited a] : (as : List a) → Tree a
 | []      => .leaf default
 | x :: xs =>
   if h : xs.length = 0 then
    .leaf x
   else
    let p := halve₁ (x :: xs)
    have : (halve₁ (x :: xs)).1.length < xs.length + 1 :=
     by simp [length_halve_fst]; omega
    have : (halve₁ (x :: xs)).2.length < xs.length + 1 :=
     by simp [length_halve_snd]; omega
    .node (mkTree p.1) (mkTree p.2)
 termination_by xs => xs.length

def mkTree₁ {a : Type} [Inhabited a] : List a → Tree a
 | [] => .leaf default
 | xs =>
   unwrap (until' single (pairWith .node) (xs.map .leaf)) |>.getD default


def cost : Tree Nat → Nat
 | Tree.leaf x     => x
 | Tree.node t₁ t₂ => 1 + Nat.max (cost t₁) (cost t₂)


def extend {a : Type} (x : a) : Tree a → List (Tree a)
 | Tree.leaf y     => [.node (.leaf x) (.leaf y)]
 | Tree.node t₁ t₂ =>
   [.node (.leaf x) (.node t₁ t₂)] ++ (extend x t₁).map (.node · t₂)


def mkTrees {a : Type} [Inhabited a] : List a → List (Tree a)
 | []      => []
 | [x]     => [Tree.leaf x]
 | x :: xs => concatMap (extend x) (mkTrees xs)


/- this should be defined only for nonempty lists -/
def foldrn {α β : Type} [Inhabited β] (f : α → β → β) (g : α → β) : List α → β
 | []      => default
 | [x]     => g x
 | x :: xs => f x (foldrn f g xs)

def mkTrees₁ {a : Type} [Inhabited a] : List a → List (Tree a) :=
 foldrn (concatMap ∘ extend) (wrap ∘ .leaf)


def Forest (a : Type) : Type := List (Tree a)


def foldl1 [Inhabited a] (f : a → a → a) : List a → a
  | []    => default
  | x::xs => xs.foldl f x

def rollup [Inhabited (Tree a)] : List (Tree a) → Tree a :=
  foldl1 .node

def spine {a : Type} : Tree a → List (Tree a)
 | .leaf x   => [.leaf x]
 | .node u v => spine u ++ [v]

example [Inhabited a] (ts : List (Tree a)) :
 spine (rollup ([Tree.leaf x] ++ ts)) = [Tree.leaf x] ++ ts := by
  induction ts with
  | nil =>
    simp [rollup, foldl1, spine]
  | cons t ts ih =>
    simp [rollup, foldl1, List.foldl, spine]
    simp [rollup, foldl1] at ih
    sorry


def extend₁ {a : Type} [Inhabited a] (x : a) (ts : Forest a) : List (Forest a) :=
  (List.range' 1 ts.length).map
    (λ i => .leaf x :: rollup (ts.take i) :: ts.drop i)

def mkForests {a : Type} [Inhabited a] : List a → List (Forest a) :=
 foldrn (concatMap ∘ extend₁) (wrap ∘ wrap ∘ .leaf)

def mkTrees₂ {a : Type} [Inhabited a] : List a → List (Tree a) :=
 List.map rollup ∘ mkForests


def mct₀ : List Nat → Tree Nat :=
 minWith cost ∘ mkTrees₂


def scanl1 (f : a → a → a) : List a → List a
 | x :: xs => Chapter1.scanl f x xs
 | []      => []

def lcost : Tree Nat → List Nat :=
  let op (x y : Nat) : Nat := 1 + Nat.max x y
  List.reverse ∘ scanl1 op ∘ List.map cost ∘ spine


def add (x : Nat) (ts : List (Tree Nat)) : List (Tree Nat) :=
  let rec join (x : Nat) : List (Tree Nat) → List (Tree Nat)
   | [u] => [u]
   | []  => []  -- not used
   | (u :: v :: ts) =>
     if Nat.max x (cost u) < cost v then
       u :: v :: ts
     else
       join x (Tree.node u v :: ts)
  termination_by ts => ts.length
  (Tree.leaf x) :: join x ts

def mct₁ : List Nat → Tree Nat :=
 let gstep (x : Nat) : Tree Nat → Tree Nat :=
  rollup ∘ add x ∘ spine
 foldrn gstep .leaf


abbrev Pair := (Tree Nat × Nat)

def node : Pair → Pair → Pair
 | (u, c), (v, d) => (Tree.node u v, 1 + Nat.max c d)

def leaf : Nat → Pair
 | x => (Tree.leaf x, x)

def join (x : Nat) : List Pair → List Pair
 | [u] => [u]
 | []  => [] -- not used
 | u :: v :: ts =>
   if Nat.max x u.snd < v.snd then
     u :: v :: ts
   else
     join x (node u v :: ts)
 termination_by ts => ts.length

def mct : List Nat → Tree Nat :=
 let hstep (x : Nat) (ts : List Pair) : List Pair :=
  leaf x :: join x ts
 rollup ∘ List.map Prod.fst ∘ foldrn hstep (wrap ∘ leaf)


/- 8.2 Huffman coding trees -/




end Chapter8

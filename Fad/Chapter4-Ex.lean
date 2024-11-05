import Fad.Chapter4

namespace Chapter4

/- 4.2
Answer: We have smallest (a,b) = x such that f x < t ≤ f (x + 1)

But for t = 1024 and f x = x^2 below f x = t and f (x + 1) > t
-/

#eval D1.smallest (fun x => dbg_trace "fun {x}"; x * x) 1024 (0, 1024)
#eval (fun x => dbg_trace "fun {x}"; x * x) 32
#eval (fun x => dbg_trace "fun {x}"; x * x) 33


/- 4.3 

Vamos provar por indução que

T(x) = ⌈log(n-1)⌉.

Para o caso base (n=2)

T(2) = ⌈log(2-1)⌉ = ⌈log(1)⌉ = ⌈0⌉ = 0.

Supondo valido para k < n, vamos provar para n. Como ⌈(n+1)/2⌉ < n,
vale a hipotese de indução, então temos que provar que:

T(n) = ⌈log(⌈(n+1)/2⌉ -1)⌉ + 1 = ⌈log(n-1)⌉.

Podemos mostrar por desigualdade indireta, mostrando que o lado
esquerdo é menor que k se e somente o lado direito é menor que k, para
qualquer k natural.  Pelo lado direito temos que ⌈log(n-1)⌉ <= k <=>
n-1 <= 2^k.  Pelo lado esquerdo:

    ⌈log(⌈(n+1)/2⌉ -1)⌉ + 1 <= k <=> ⌈log(⌈(n+1)/2⌉ -1)⌉ <= k-1,
                                 <=> log(⌈(n+1)/2⌉ -1) <= k-1,
                                 <=> ⌈(n+1)/2⌉ -1 <= 2^(k-1),
                                 <=> ⌈(n+1)/2⌉ <= 2^(k-1) + 1,
                                 <=> (n+1)/2 <= 2^(k-1) + 1,
                                 <=> n+1 <= 2^k + 2,
                                 <=> n-1 <= 2^k.

O que completa a prova, uma vez que ambos os lados chegam na mesma
proposição.

-/


/- 4.4 : see the book -/

/- 4.6 -/

#eval D2.search₁ (λ (x, y) => x ^ 3 + y ^ 3) 1729


/- 4.7 -/

def Tree1.Tree.flatcat : (t : Tree1.Tree a) → (xs: List a) → List a
| null, xs => xs
| (node l x r), xs => l.flatcat (x :: r.flatcat xs)

def Tree1.Tree.flatten₁ (t : Tree1.Tree a) : List a :=
 t.flatcat []

#eval Tree1.mkTree [1,2,3,5] |>.flatten
#eval Tree1.mkTree [1,2,3,5] |>.flatten₁

example (t: Tree1.Tree a) :
  t.flatten = t.flatten₁ := by
  induction t with
  | null => exact rfl
  | node l x r ihl ihr =>
    simp [Tree1.Tree.flatten₁]
    simp [Tree1.Tree.flatten]
    simp [Tree1.Tree.flatcat]
    simp [ihl, ihr]
    simp [Tree1.Tree.flatten₁]
    sorry


/- 4.8
  obs: pode ser necessario mathlib? -/

open Chapter4.Tree1.Tree in

example {α : Type} (t : Chapter4.Tree1.Tree α) :
  t.height ≤ t.size ∧ t.size < 2 ^ t.height := by
 apply And.intro
 {
 induction t with
 | null => simp [height, size]
 | node t₁ x t₂ ihl ihr =>
   simp [height, size]
   sorry
 }
 {
  induction t with
  | null => simp [height,size]
  | node t₁ x t₂ ihl ihr =>
    simp [height, size]
    sorry
 }

open Chapter4.Tree1 in

example {α : Type} (t : Tree α) :
  t.height ≤ t.size ∧ t.size < 2 ^ t.height := by
 induction t with n t₁ t₂ ih_t₁ ih_t₂
  case leaf n =>
    split
    case left =>
      dsimp [Chapter3.Tree.height, Chapter3.Tree.size]
      exact nat.le_refl 1
    case right =>
      dsimp [Tree.height, Tree.size]
      exact nat.lt_succ_self 1
  case node n t₁ t₂ =>
    cases ih_t₁ with | intro ih_t₁_height ih_t₁_size
    cases ih_t₂ with | intro ih_t₂_height ih_t₂_size
    split
    case left =>
      dsimp [Tree.height, Tree.size]
      exact nat.succ_le_of_lt (max_le ih_t₁_height ih_t₂_height)
    case right =>
      dsimp [Tree.height, Tree.size]
      calc
        n < 2 ^ (1 + max t₁.height t₂.height) : by linarith [ih_t₁_size, ih_t₂_size]
        _ = 2 ^ t.height : by rw max_comm


/- 4.10 -/

def partition3 (y : Nat) (xs : List Nat) : (List Nat × List Nat × List Nat) :=
 let op x acc :=
   let (us, vs, ws) := acc
     if      x < y then (x :: us, vs, ws)
     else if x = y then (us, x :: vs, ws)
     else (us, vs, x :: ws)
 xs.foldr op ([], [], [])

#eval partition3 3 [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

partial def Tree1.mkTree₁ : (xs : List Nat) → Tree1.Tree (List Nat)
| [] => Tree1.Tree.null
| (x :: xs) =>
   match partition3 x (x :: xs) with
   | (us, vs, ws) => Tree1.Tree.node (mkTree₁ us) vs (mkTree₁ ws)

#eval Tree1.mkTree₁ [1,2,2,3,5] |>.flatten


/- 4.16 -/

namespace Tree2

def balanceL (t₁ : Tree a) (x : a) (t₂ : Tree a) : Tree a :=
 match t₂ with
 | Tree.null => Tree.null
 | Tree.node _ l y r =>
   if l.height ≥ t₁.height + 2
   then balance (balanceL t₁ x l) y r
   else balance (node t₁ x l) y r

end Tree2

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

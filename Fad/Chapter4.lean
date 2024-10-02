
import Fad.Chapter1

namespace Chapter4

def search₀ (f : Nat → Nat) (t : Nat) : List Nat :=
 List.foldl (fun xs x => if t = f x then x :: xs else xs) []
  (List.range <| t + 1)

#eval search₀ (fun x => x) 10


def search₁ (f : Nat → Nat) (t : Nat) : List Nat :=
  seek (0, t)
 where
  acc xs x := if t = f x then x :: xs else xs
  seek : (Nat × Nat) → List Nat
  | (a, b) => List.foldl acc [] <| List.range' a (b - a + 1)

#eval search₁ (fun x => x) 10


partial def search₂ (f : Nat → Nat) (t : Nat) : List Nat :=
 let rec seek (a b : Nat) : List Nat :=
  -- dbg_trace "seek {a} {b}"
  let m := (a + b) / 2
   if a > b then  []
   else if t < f m then seek a (m - 1)
   else if t = f m then [m]
   else seek (m + 1) b
 seek 0 t

#eval search₂ (fun x => x) 114


def bound (f : Nat → Nat) (t : Nat) : (Int × Nat) :=
  if t ≤ f 0 then (-1, 0) else (b / 2, b)
 where
  b := Chapter1.until' done (· * 2) 1
  done b := t ≤ f b

partial def smallest (p : Int × Nat) (f : Nat → Nat) (t : Nat) : Nat :=
 let (a, b) := p
  if a + 1 = b then b
  else if t ≤ f m.toNat then smallest (a, m.toNat) f t
  else smallest (m, b) f t
 where
  m := (p.1 + p.2) / 2

def search₃ (f : Nat → Nat) (t : Nat) : List Nat :=
  if f x = t then [x] else []
 where
  x := smallest (bound f t) f t

#eval bound (fun x => dbg_trace "fun {x}"; 2^x) 1024
#eval search₃ (fun x => dbg_trace "fun {x}"; 2^x) 1024


end Chapter4

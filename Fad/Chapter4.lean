
import Fad.Chapter1

namespace Chapter4

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
  -- dbg_trace "seek {a} {b}"
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

#eval bound (fun x => dbg_trace "fun {x}"; x) 1024
#eval search₃ (fun x => dbg_trace "fun {x}"; x) 1024

end D1


namespace D2

def search₀ (f : (Nat × Nat) → Nat) (t : Nat) : List (Nat × Nat) :=
 List.filter (λ p => t = f p) allPairs
 where
  as := (List.range $ t + 1)
  allPairs := Chapter1.concatMap (λ x => List.map (λ y => (x, y)) as) as

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

end Chapter4

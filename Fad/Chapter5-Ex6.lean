import Fad.Chapter5


-- version that doesn't use qsort inside of the help function.
-- Because of it's unnecessary complexity, I haven't focused in
-- proving it's termination
def qsort1 [LT α] [DecidableRel (@LT.lt α _)] (y : List α) : List α :=
  match y with
  | []       => []
  | x :: xs  => help x xs [] []
where
  help (y : α) (ys : List α) (us vs : List α) : List α :=
    match ys with
    | [] => us ++ [y] ++ vs
    | [a] =>
      if a < y then
      match h: us, h1: vs with
      | [], [] => [a,y]
      | bs, [] =>
      have : bs.length < 1 := by rw [←h]; sorry
      (help a bs [] []) ++ [y]
      | [], b::bs =>
      have : bs.length < 1 := by sorry
      [a, y] ++ (help b bs [] [])
      | bs, c::cs =>
        have : bs.length < 1 := by sorry
        (help a (bs) [] []) ++ [y] ++ (help c cs [] [])
      else
      match us, vs with
      | [], [] => [y,a]
      | b::bs, [] => (help b bs [] []) ++ [y,a]
      | [], bs => [y] ++ (help a bs [] [])
      | b::bs, cs =>
        (help b bs [] []) ++ [y] ++ (help a cs [] [])
    | a :: as =>
      if a < y then
        help y as (a :: us) vs
      else
        help y as us (a :: vs)


  -- book's definition, that also uses match and makes it harder for Lean to see termination
  def qsort2 [LE α] [DecidableRel (@LE.le α _)] (y : List α) : List α :=
  match h1 : y with
  | [] => []

  | x::xs => help x xs [] [] where

  help (x : α) (ys us vs: List α) : List α:=
    match h : ys with
    | [] =>
    have h: ys.length = 0 := by exact List.length_eq_zero.mpr h
    qsort2 us ++ [x] ++ qsort2 vs
    | y::xs => if x ≤ y
    then
      help x xs us (y::vs)
    else
      help x xs (y::us) vs


  -- my new definition, based in the book and the idea of changing matches by ifs
mutual
  def qsort3 [LE α] [DecidableEq α] [DecidableRel (@LE.le α _)] (y : List α) : List α :=
    if  h₁ : y = [] then []
    else
      let x::xs := y
      help x xs [] []
   termination_by y

  def help (x : α) (ys us vs: List α) [LE α] [DecidableEq α] [DecidableRel (@LE.le α _)] : List α:=
    if h₂ : ys = [] then
      (qsort3  us) ++ [x] ++ (qsort3 vs)
    else
      let y::xs := ys
    if h₅ : x ≤ y then
      help x xs us (y::vs)
    else
      help x xs (y::us) vs
    termination_by ys
end


-- tried to create an argument that would decrease every time the function is called; unfortunately, I
-- still couldn't prove the termination
mutual
  def qsort₁ [LE α] [DecidableEq α] [DecidableRel (@LE.le α _)] (n : Nat) (y : List α) : List α :=
    if h₁ : n = 0 then y else
      if  h₂ : y.length = 0 then []
      else
        let x::xs := y
        help₁ n x xs [] []
   termination_by n

  def help₁  (t : Nat) (x : α) (ys us vs: List α) [LE α] [DecidableEq α] [DecidableRel (@LE.le α _)] : List α:=
    if h₃ : t = 0 then x::ys else
    if h₄ : ys = [] then
      (qsort₁ (t - 1 - vs.length) us) ++ [x] ++ (qsort₁ (t- 1 - us.length) vs)
    else
      let y::xs := ys
    if h₅ : x ≤ y then
      help₁ t x xs us (y::vs)

    else
      help₁ t x xs (y::us) vs
    termination_by t
end

mutual
  def qsort₂ [LE α] [DecidableEq α] [DecidableRel (@LE.le α _)] (n : Nat) (y : List α) : List α :=
    if n = 0 then y else
      if  _ : y.length = 0 then []
      else
        let x::xs := y
        help₂ n x xs [] []
   termination_by (n, sizeOf y)

  def help₂  (t : Nat) (x : α) (ys us vs: List α) [LE α] [DecidableEq α] [DecidableRel (@LE.le α _)] : List α:=
    if t = 0 then x::ys else
    if _ : ys = [] then
      (qsort₂ (t - 1 - vs.length) us) ++ [x] ++ (qsort₂ (t- 1 - us.length) vs)
    else
      let y::xs := ys
    if  x ≤ y then
      help₂ t x xs us (y::vs)

    else
      help₂ t x xs (y::us) vs
    termination_by (t, sizeOf ys)
end


def list (y : List α) : Nat × List α := (y.length, y)

abbrev l1 (x : List α):= (list x).1
abbrev l2 (x : List α):= (list x).2
abbrev q (x : List α) [LE α] [DecidableEq α] [DecidableRel (@LE.le α _)]:= qsort3 (l1 x) (l2 x)

#eval!  q [1,2,3,4,5,1,6,3,6,3] |> List.length
#eval!  q [1,2,3,4,5,1,6,3,6,3]
#eval!  [1,2,3,4,5,1,6,3,6,3] |> List.length

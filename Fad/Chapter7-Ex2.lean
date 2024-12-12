/- import Fad.Chapter7-Ex "unexpected token '-'; expected command"-/
-- Can't import ^ due to "-", I'll just paste the old version's code here

-- Old version
def minsWith {α β : Type} [Ord β] (f : α → β) (xs : List α) : List α :=
  let step (x : α) (ys : List α) : List α :=
    match ys with
    | [] => [x]
    | y :: ys =>
      match compare (f x) (f y) with
      | Ordering.lt => [x]
      | Ordering.eq => x :: y :: ys
      | Ordering.gt => y :: ys
  xs.foldr step []

-- Optimized version
def minsWith' {α β : Type} [Ord β] (f : α → β) (xs : List α) : List α :=
  let step (x : β × α) (ys : List (β × α)) :=
    match ys with
    | [] => [x]
    | y :: ys =>
      match compare (x.fst) (y.fst) with
      | Ordering.lt => [x]
      | Ordering.eq => x :: y :: ys
      | Ordering.gt => y :: ys
  xs.map tuple |>.foldr step [] |>.map (·.snd)
    where tuple x := (f x, x)

theorem minsWith_eq_minsWith' {α β : Type} [Ord β] (f : α → β) (xs : List α) :
  minsWith f xs = minsWith' f xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp [minsWith, minsWith']
      sorry


#eval minsWith (fun x => dbg_trace "f {x}"; x % 5) (List.range 15)
#eval minsWith' (fun x => dbg_trace "f {x}"; x % 5) (List.range 15)

#eval minsWith (fun x => dbg_trace "f {x}"; x / 2) [10, 20, 30, 40, 50]
#eval minsWith' (fun x => dbg_trace "f {x}"; x / 2) [10, 20, 30, 40, 50]

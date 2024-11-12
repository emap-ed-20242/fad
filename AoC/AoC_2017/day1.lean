--Problem: https://adventofcode.com/2017/day/1

namespace AoC2017D1

def input_day1 : String := include_str "../../data/AoC2017_day1.txt"

def remove_line_feed (s : String) : String :=
  s.replace "\x0d" ""

def input_task := remove_line_feed input_day1

-- Parte 1
def ChToDig (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.val.toNat - '0'.val.toNat else 0

def capSol (inp : String) : Nat :=
  let ch := inp.toList
  let len := ch.length
  let res := ch.enum.foldl (fun acc (i, curr) =>
    let nxt := ch[(i + 1) % len]!
    let crrDig := ChToDig curr
    let nxtDig := ChToDig nxt
    if crrDig == nxtDig then acc + crrDig else acc
  ) 0
  res

#eval capSol input_task

-- Parte 2
def capSol2 (inp : String) : Nat :=
  let ch := inp.toList
  let len := ch.length
  let stp := len / 2
  let res := ch.enum.foldl (fun acc (i, crr) =>
    let nxt := ch[(i + stp) % len]!
    let crrDig := ChToDig crr
    let nxtDig := ChToDig nxt
    if crrDig == nxtDig then acc + crrDig else acc
  ) 0
  res

#eval capSol2 input_task

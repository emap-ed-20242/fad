--Problem: https://adventofcode.com/2017/day/1

namespace AoC2017D1

def inp : String := include_str "../../data/AoC2017_day1.txt"

def rmLf (s : String) : String :=
  s.replace "\x0d" ""

def inpStr := rmLf inp

-- Parte 1
def chToDig (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.val.toNat - '0'.val.toNat else 0

def solve1 (str : String) : Nat :=
  let ch := str.toList
  let len := ch.length
  let res := ch.enum.foldl (fun acc (i, cur) =>
    let nxt := ch[(i + 1) % len]!
    let curDig := chToDig cur
    let nxtDig := chToDig nxt
    if curDig == nxtDig then acc + curDig else acc
  ) 0
  res

#eval solve1 inpStr

-- Parte 2
def solve2 (str : String) : Nat :=
  let ch := str.toList
  let len := ch.length
  let step := len / 2
  let res := ch.enum.foldl (fun acc (i, cur) =>
    let nxt := ch[(i + step) % len]!
    let curDig := chToDig cur
    let nxtDig := chToDig nxt
    if curDig == nxtDig then acc + curDig else acc
  ) 0
  res

#eval solve2 inpStr

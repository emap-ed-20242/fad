-- Problem: https://adventofcode.com/2017/day/5

namespace AoC2017D5

def inp : String := include_str "../../data/AoC2017_day5.txt"

def rmLf (s : String) : String :=
  s.replace "\x0d" ""

def toIntArr (s : String) : Array Int :=
  (s.split (· == '\n') |>.filterMap String.toInt?).toArray

def inpArr : Array Int := toIntArr (rmLf inp)

#eval inpArr

-- Parte 1
def stepsToExit1 (jmp : Array Int) : Nat :=
  let rec jump (arr : Array Int) (idx : Int) (steps : Nat) : Nat :=
    if idx < 0 || idx >= arr.size then
      steps
    else
      let off := arr[idx.toNat]!
      let newArr := arr.set! idx.toNat (off + 1)
      jump newArr (idx + off) (steps + 1)
  jump jmp 0 0

#eval! stepsToExit1 inpArr  -- 358131

-- Parte 2
def stepsToExit2 (jmp : Array Int) : Nat :=
  let rec jump (arr : Array Int) (idx : Int) (steps : Nat) : Nat :=
    if idx < 0 || idx >= arr.size then
      steps
    else
      let off := arr[idx.toNat]!
      let newOff := if off >= 3 then off - 1 else off + 1
      let newArr := arr.set! idx.toNat newOff
      jump newArr (idx + off) (steps + 1)
  jump jmp 0 0

#eval! stepsToExit2 inpArr  -- 25558839

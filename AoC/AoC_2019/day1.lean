-- Problem: https://adventofcode.com/2019/day/1

namespace AoC2019D1


def content : String := include_str "../../data/AoC2019_day1.txt"
def weights_list : List Nat := content.splitOn "\n" |>.map String.toNat!


#eval content
#eval weights_list


--- Part I


def get_required_gas_I ( ns : List Nat ) : Nat :=
  ns.foldr (λ n acc => n/3 - 2 + acc) 0


#eval get_required_gas_I weights_list --- 3390596


--- Part II


def recursive_fuction ( n: Nat ) :  Nat :=
  if (n/3-2) = 0 then 0 else
    recursive_fuction ( n / 3 - 2) + (n/3-2)


def get_required_gas_II ( ns : List Nat ) : Nat :=
  ns.foldr (λ n acc => recursive_fuction n + acc) 0


#eval get_required_gas_II weights_list  --- 5083024


end AoC2019D1

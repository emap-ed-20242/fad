partial def qsort₁ [LT a] [DecidableRel (· < · : a → a → Prop)] : List a → List a
| [] => []
| (x :: xs) =>
  let p := xs.partition (· < x)
  (qsort₁ p.1) ++ [x] ++ (qsort₁ p.2)

def suit_order : String → Nat
| "S" => 0
| "H" => 1
| "D" => 2
| "C" => 3
| _ => 4

def rank_order : String → Nat
| "A" => 0
| "K" => 1
| "Q" => 2
| "J" => 3
| "T" => 4
| "9" => 5
| "8" => 6
| "7" => 7
| "6" => 8
| "5" => 9
| "4" => 10
| "3" => 11
| "2" => 12
| _ => 13

def card_key (card : String × String ) : (Nat × Nat) :=
  (suit_order card.1, rank_order card.2)

def sort_bridge_hand (hand : List (String × String)) : List String :=
  qsort₁ (λ a b => card_key a < card_key b) hand

#eval sort_bridge_hand [("S","A"), ("S","Q"), ("S","9"), ("S","8"), ("S","2"), ("H","K"), ("H","5"), ("H","3"), ("H","2"), ("C","A"), ("C","T"), ("C","7"), ("C","2")]

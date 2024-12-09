import Fad.Chapter1
import Fad.Chapter3

inductive bTree (α : Type) : Type where
 | nil
 | node (h : Nat) (t₁ : bTree α) (n : α) (t₂ : bTree α) : bTree α
 deriving Repr

 def height : (a : bTree α) -> Nat
 | bTree.nil => 0
 | bTree.node x _ _ _ => x

#eval bTree.node (height (bTree.nil : bTree Nat) + 1) (bTree.nil : bTree Int) 4 bTree.nil

def node (l : bTree α) (x : α) (r : bTree α): bTree α :=
bTree.node h l x r where h := 1 + (max (height l) (height r))

#eval node bTree.nil 4 bTree.nil

def bias(t : bTree α) : Int :=
match t with
|.nil => 0
|.node _ l _ r => height l - height r

#eval bias (node bTree.nil 4 (node bTree.nil 4 bTree.nil))

def abs (n : Int) : Int := if n < 0 then (0 - n) else n

#eval abs (-4)

def rotr (t : bTree α) : bTree α :=
match t with
|.nil => .nil
|.node _ (.node _ ll y rl) x r => node ll y (node rl x r)
|.node _ .nil _ _ => .nil -- you can't rotate this tree to the right

def rotl (t : bTree α) : bTree α :=
match t with
|.nil => .nil
|.node _ ll y (.node _ lrl z rrl) => node (node ll y lrl) z rrl
|.node _ _ _ .nil => .nil -- you can't rotate this tree to the left

def balance (t1 : bTree α)  (x : α)  (t2 : bTree α) : bTree α :=
if abs (h1 - h2) ≤ 1 then node t1 x t2 else if h1 == h2 + 2 then rotateR t1 x t2 else rotateL t1 x t2
  where
  h1 := height t1
  h2 := height t2
  rotateR t1 x t2 := if 0 <= bias t1 then rotr (node t1 x t2) else rotr (node (rotl t1) x t2)
  rotateL t1 x t2 := if bias t2 <= 0 then rotl (node t1 x t2) else rotl (node t1 x (rotr t2))

def insert {α : Type} [LT α] [DecidableRel (@LT.lt α _)] : (x : α) -> bTree α -> bTree α
| x, .nil => node bTree.nil x bTree.nil
| x, .node h l y r =>
  if x < y  then balance (insert x l) y r else
  if x > y then balance l y (insert x r) else .node h l y r



def mkbTree (xs : List α) [LT α] [DecidableRel (@LT.lt α _)]: bTree α :=
mkbTree xs where
mkbTree := Chapter1.foldr insert (bTree.nil : bTree α)

#eval mkbTree [1,2,3,4,5,6,7,8] -- note that the height of the first node is 4

def bTree.toList : bTree α -> List α
| .nil => []
| .node _ l x r => (bTree.toList l) ++ [x] ++ (bTree.toList r)

#eval (mkbTree [1,2,3,4]).toList

abbrev Set (α : Type) : Type := bTree α

#eval (mkbTree [1,2,3] : Set Nat)

def pair  (f : α -> β) (p : α × α) : (β × β) := (f p.1, f p.2)

-- set -> list -> (list <= x, list >x) -> pair mktree (xs, ys)
def split (x : α) (t : Set α) [LE α] [LT α] [DecidableRel (@LT.lt α _)] [DecidableRel (@LE.le α _)]: Set α × Set α :=
pair (λ xs => mkbTree xs) (Chapter1.filter (· <= x) (bTree.toList t), Chapter1.filter (· > x) (bTree.toList t))
-- needed the lambda because of type errors. LT and LE are typeclasses to
-- make sure that α holds less than and greater than comparisons
-- this is my answer to the exercise, the book one is split x = pair mktree ∘ partition (≤ x) · flatten, defined below
def split2 (x : α) (t : Set α) [LE α] [LT α] [DecidableRel (@LT.lt α _)] [DecidableRel (@LE.le α _)]: Set α × Set α :=
pair (λ xs => mkbTree xs) $ List.partition (· ≤ x) $ bTree.toList t

#eval split2 2 (mkbTree [1,2,3,4] : Set Nat)
#eval split 2 (mkbTree [1,2,3,4] : Set Nat)
#check split 2 (mkbTree [1,2,3,4] : Set Nat)

import Fad.Chapter4

namespace Chapter4

inductive Tree (α : Type) : Type
| null : Tree α
| node : Tree α → α → Tree α → Tree α

partial def union {α : Type} [DecidableEq α] [Ord α] : Tree α → Tree α → Tree α
| Tree.null, t2 => t2
| t1, Tree.null => t1
| (Tree.node l1 x1 r1), (Tree.node l2 x2 r2) =>
    if x1 = x2 then
      Tree.node (union l1 l2) x1 (union r1 r2)
    else if compare x1 x2 == Ordering.lt then
      Tree.node (union l1 (Tree.node l2 x2 r2)) x1 r1
    else
      Tree.node l1 x1 (union r1 (Tree.node l2 x2 r2))

end Chapter4

import Fad.Chapter3
namespace Chapter4



-- Define the theorem to prove
theorem height_le_size_lt_two_pow_height {α : Type} (t : Chapter3.Tree α) :
  t.height ≤ t.size ∧ t.size < 2 ^ t.height := by
 induction t with n t₁ t₂ ih_t₁ ih_t₂
  case leaf n =>
    split
    case left =>
      dsimp [Chapter3.Tree.height, Chapter3.Tree.size]
      exact nat.le_refl 1
    case right =>
      dsimp [Tree.height, Tree.size]
      exact nat.lt_succ_self 1
  case node n t₁ t₂ =>
    cases ih_t₁ with | intro ih_t₁_height ih_t₁_size
    cases ih_t₂ with | intro ih_t₂_height ih_t₂_size
    split
    case left =>
      dsimp [Tree.height, Tree.size]
      exact nat.succ_le_of_lt (max_le ih_t₁_height ih_t₂_height)
    case right =>
      dsimp [Tree.height, Tree.size]
      calc
        n < 2 ^ (1 + max t₁.height t₂.height) : by linarith [ih_t₁_size, ih_t₂_size]
        _ = 2 ^ t.height : by rw max_comm

end Chapter4

import Fad.Chapter4
import Fad.Chapter3
namespace Chapter4



theorem size_bound : ∀ t : Chapter3.Tree α, t.height ≤ t.size ∧ t.size < 2 ^ t.height := by
  intro t
  induction t with
  | leaf val =>
    simp [Chapter3.Tree.size, Chapter3.Tree.height]
    apply And.intro

    · exact Nat.le_refl 1

    · exact Nat.one_lt_two
  | node n l r ihl ihr =>
    simp [Chapter3.Tree.size, Chapter3.Tree.height]
    cases ihl with
    | intro h₁ h₂ =>
      cases ihr with
      | intro h₃ h₄ =>

        have height_le_size : t.height ≤ t.size := by
          apply Nat.succ_le_succ
          exact Nat.le_max_of_le_left h₁

        have size_lt_pow_height : t.size < 2 ^ t.height := by
          have h₅ := Nat.pow_lt_pow_succ 2 (Nat.max_le_iff.mp (Nat.le_max_of_le_left h₃))
          rw [Nat.pow_succ]
          apply Nat.lt_of_le_of_lt
          apply Nat.add_le_add
          · apply Nat.le_add_left
          · apply Nat.le_add_right
          exact Nat.add_lt_add h₂ h₄ h₅
        exact ⟨height_le_size, size_lt_pow_height⟩


end Chapter4

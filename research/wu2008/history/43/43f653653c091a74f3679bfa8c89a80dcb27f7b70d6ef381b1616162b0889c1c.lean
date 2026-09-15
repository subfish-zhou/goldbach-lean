import MathlibNt.Wu2004MeanValue.OriginalTriples
import MathlibNt.Wu2004MeanValue.OriginalTailQuotients

/-!
# Literal large-product bad triples

The strict product cutoff complements the closed cutoff in `originalTriples`.
The carrier retains all three prime coordinates, including squares.
-/

namespace Wu2004MeanValue

open Classical Finset
noncomputable section

def originalLargeTriples (N : ℕ) (a η : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (range (N + 1) ×ˢ (range (N + 1) ×ˢ range (N + 1))).filter
    (fun t => t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧
      N = t.1 + t.2.1 * t.2.2 ∧ t.2.1 ≤ t.2.2 ∧
      (t.2.2 : ℝ) ^ (a - 1) < t.2.1 ∧ η * N < (t.2.1 : ℝ) * t.2.2)

def originalLargeTripleCount (N : ℕ) (a η : ℝ) : ℕ :=
  (originalLargeTriples N a η).card

theorem mem_originalLargeTriples {N p r q : ℕ} {a η : ℝ} :
    (p, r, q) ∈ originalLargeTriples N a η ↔
      p.Prime ∧ r.Prime ∧ q.Prime ∧ N = p + r * q ∧ r ≤ q ∧
        (q : ℝ) ^ (a - 1) < r ∧ η * N < (r : ℝ) * q := by
  simp only [originalLargeTriples, mem_filter, mem_product, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hr : r ≤ r * q := Nat.le_mul_of_pos_right r h.2.2.1.pos
    have hq : q ≤ r * q := Nat.le_mul_of_pos_left q h.2.1.pos
    exact ⟨⟨by omega, by omega, by omega⟩, h⟩

end
end Wu2004MeanValue

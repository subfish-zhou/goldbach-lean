import MathlibNt.SieveTheory.LiLiuGoldbachG12LowRectangle
import MathlibNt.SieveTheory.LiLiuGoldbachG12BoundingSieve
import MathlibNt.SieveTheory.LiLiuPrereqWFExternalSieve
import MathlibNt.SieveTheory.LiLiuFouvryG9WFBridge


noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace G12RectangleWF

abbrev Atom := (ℕ × ℕ) × ℕ

def multiplicity (N m : ℕ) : ℕ :=
  goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m


def output (N : ℕ) (a : Atom) : ℕ := N-a.1.2*a.1.1


/-- The gcd gate is explicit and signed, and is not paid in this module. -/
def gate (N : ℕ) (S : Finset (ℕ × ℕ)) (Q : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ reducedModuli Q (N : ℤ), c d *
    ((∑ p ∈ S, if ¬ (p.1*p.2).Coprime d
      then goldbachG12NormalizedCoefficient N p.1 else 0) / (d.totient : ℝ))

def common (N : ℕ) (S : Finset (ℕ × ℕ)) (Q : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ reducedModuli Q (N : ℤ), c d *
    ((∑ p ∈ S, if Int.ModEq d ((p.1 : ℤ)*p.2) (N : ℤ)
      then goldbachG12NormalizedCoefficient N p.1 else 0) -
      (∑ p ∈ S, goldbachG12NormalizedCoefficient N p.1) / (d.totient : ℝ))

/-- Exact C2 coprime-main decomposition, with no absolute values or masks. -/
theorem common_eq_discrepancy_sub_gate (N : ℕ) (S : Finset (ℕ × ℕ))
    (Q : Finset ℕ) (c : ℕ → ℝ) :
    common N S Q c = G12LowRectangle.discrepancy N S Q c - gate N S Q c := by
  unfold common G12LowRectangle.discrepancy gate
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  have hsplit : (∑ p ∈ S, goldbachG12NormalizedCoefficient N p.1) =
      (∑ p ∈ S, if (p.1*p.2).Coprime d then goldbachG12NormalizedCoefficient N p.1 else 0) +
      (∑ p ∈ S, if ¬ (p.1*p.2).Coprime d then goldbachG12NormalizedCoefficient N p.1 else 0) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    by_cases h : (p.1*p.2).Coprime d <;> simp [h]
  rw [hsplit]
  ring

end G12RectangleWF

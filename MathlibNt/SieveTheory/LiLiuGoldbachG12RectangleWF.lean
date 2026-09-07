import MathlibNt.SieveTheory.LiLiuGoldbachG12LowRectangleC2
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

/-- Actual repeated labels, not a replacement of the normalized weight by one. -/
def labels (N : ℕ) (ε : ℝ) (M T : ℕ) : Finset Atom :=
  ((G12LowRectangle.rectangle N ε M T).sigma
    (fun p => range (multiplicity N p.1))).image (fun p => (p.1,p.2))

def output (N : ℕ) (a : Atom) : ℕ := N-a.1.2*a.1.1

def mass (N : ℕ) (ε : ℝ) (M T : ℕ) : ℝ :=
  ∑ p ∈ G12LowRectangle.rectangle N ε M T, goldbachG12NormalizedCoefficient N p.1

/-- Every test retains precisely the original factor 400. -/
theorem labels_test (N : ℕ) (ε : ℝ) (M T : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ a ∈ labels N ε M T, f a.1) =
      400 * ∑ p ∈ G12LowRectangle.rectangle N ε M T,
        goldbachG12NormalizedCoefficient N p.1 * f p := by
  rw [G12LowRectangle.restore_multiplicity]
  unfold labels
  rw [sum_image]
  · rw [sum_sigma]
    simp [multiplicity, mul_comm]
  · intro a _ b _ hab
    cases a
    cases b
    obtain ⟨h₁,h₂⟩ := Prod.mk.inj hab
    cases h₁
    cases h₂
    rfl

theorem labels_card (N : ℕ) (ε : ℝ) (M T : ℕ) :
    ((labels N ε M T).card : ℝ) = 400 * mass N ε M T := by
  simpa [mass] using labels_test N ε M T (fun _ => 1)

def outputWeight (N : ℕ) (ε : ℝ) (M T n : ℕ) : ℝ :=
  ∑ p ∈ (G12LowRectangle.rectangle N ε M T).filter (fun p => N-p.2*p.1=n),
    goldbachG12NormalizedCoefficient N p.1

/-- Only the finite weighted mother changes; B10's local density is inherited. -/
def sieve (N : ℕ) (hEven : Even N) (ε Z : ℝ) (M T : ℕ) : BoundingSieve :=
  { goldbachB10BoundingSieve N hEven 0 0 0 Z (mass N ε M T) with
    support := (G12LowRectangle.rectangle N ε M T).image (fun p => N-p.2*p.1)
    weights := outputWeight N ε M T
    weights_nonneg := fun _ => sum_nonneg
      (fun p _ => (goldbachG12NormalizedCoefficient_bounds N p.1).1) }

theorem sieve_nu (N : ℕ) (hEven : Even N) (ε Z : ℝ) (M T : ℕ) :
    (sieve N hEven ε Z M T).nu =
      (goldbachB10BoundingSieve N hEven 0 0 0 Z (mass N ε M T)).nu := rfl

theorem sieve_prodPrimes (N : ℕ) (hEven : Even N) (ε Z : ℝ) (M T : ℕ) :
    (sieve N hEven ε Z M T).prodPrimes = goldbachB10ProdPrimes N Z := rfl

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

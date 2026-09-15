import MathlibNt.AnalyticNumberTheory.Vaughan.ProductionVaughanTypeIIRectangularMaximalShell
import MathlibNt.AnalyticNumberTheory.Vaughan.ProductionVaughanTypeIIRectangularCoeffBounds

/-!
# Explicit honest bound for one rectangular Vaughan Type-II shell

This leaf scalarizes the two coefficient energies and their `L¹` mass.  It
retains the actual `largeSieveBound` used by `rankOneRectangularLSRHS`.
In particular it does not identify that weak large-sieve constant with the
smaller, canonical-looking quantity `D + Q^2`.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Right endpoint of the Type-II rectangle. -/
def vaughanTypeIIRectangularX (N k : ℕ) : ℕ := N / 2 ^ k

/-- Length of the left dyadic rectangle. -/
def vaughanTypeIIRectangularD (k : ℕ) : ℕ := 2 ^ k

/-- Length of the right rectangle. -/
def vaughanTypeIIRectangularT (N k l : ℕ) : ℕ :=
  vaughanTypeIIRectangularX N k - 2 ^ l + 1

/-- Explicit upper bound for the right coefficient energy. -/
def vaughanTypeIIRectangularEright (N k : ℕ) : ℝ :=
  27 * (vaughanTypeIIRectangularX N k : ℝ) *
    Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5

/-- The literal `(D+Q²)` expression.  It is recorded for comparison only: the
current definition of `rankOneRectangularLSRHS` uses `largeSieveBound`, which is
strictly wider and cannot honestly be bounded by this expression in general. -/
def vaughanTypeIIRectangularCanonicalRexp (N k l Q : ℕ) : ℝ :=
  Real.sqrt ((((vaughanTypeIIRectangularD k : ℕ) : ℝ) + (Q : ℝ) ^ 2) *
      (vaughanTypeIIRectangularD k : ℝ)) *
    Real.sqrt ((((vaughanTypeIIRectangularT N k l : ℕ) : ℝ) + (Q : ℝ) ^ 2) *
      vaughanTypeIIRectangularEright N k)

/-- Honest explicit rank-one majorant for the large-sieve constant currently
present in `rankOneRectangularLSRHS`. -/
def vaughanTypeIIRectangularRexp (N k l Q : ℕ) : ℝ :=
  Real.sqrt (largeSieveBound (vaughanTypeIIRectangularD k)
      (1 / (Q : ℝ) ^ 2) * (vaughanTypeIIRectangularD k : ℝ)) *
    Real.sqrt (largeSieveBound (vaughanTypeIIRectangularT N k l)
      (1 / (Q : ℝ) ^ 2) * vaughanTypeIIRectangularEright N k)

/-- Explicit Cauchy--Schwarz majorant for the coefficient `L¹` mass. -/
def vaughanTypeIIRectangularL1exp (N k l : ℕ) : ℝ :=
  Real.sqrt ((vaughanTypeIIRectangularD k : ℝ) *
      (vaughanTypeIIRectangularD k : ℝ)) *
    Real.sqrt ((vaughanTypeIIRectangularT N k l : ℝ) *
      vaughanTypeIIRectangularEright N k)

private theorem active_geometry
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    2 ^ l ≤ N / 2 ^ k := by
  have hcorner : 2 ^ k * 2 ^ l ≤ N :=
    (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2
  exact (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2
    (by simpa [mul_comm] using hcorner)

private theorem left_upper_endpoint (k : ℕ) :
    (2 ^ k : ℤ) - 1 + (2 ^ k : ℕ) =
      (((2 ^ (k + 1) - 1 : ℕ) : ℤ)) := by
  have hp : 1 ≤ 2 ^ (k + 1) :=
    (Nat.one_le_iff_ne_zero).2 (pow_ne_zero _ (by norm_num))
  rw [Nat.cast_sub hp, pow_succ]
  push_cast
  ring

private theorem right_upper_endpoint
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    (2 ^ l : ℤ) - 1 + (N / 2 ^ k - 2 ^ l + 1 : ℕ) =
      ((N / 2 ^ k : ℕ) : ℤ) := by
  have hl := active_geometry N u v k l hactive
  rw [Nat.cast_add, Nat.cast_sub hl]
  push_cast
  ring

private theorem rectangular_cards
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    (Finset.Icc ((2 ^ k : ℕ) : ℤ)
        (((2 ^ (k + 1) - 1 : ℕ) : ℤ))).card = 2 ^ k ∧
    (Finset.Icc ((2 ^ l : ℕ) : ℤ)
        ((N / 2 ^ k : ℕ) : ℤ)).card =
      N / 2 ^ k - 2 ^ l + 1 := by
  have hl := active_geometry N u v k l hactive
  constructor
  · rw [Int.card_Icc]
    have hp : 1 ≤ 2 ^ (k + 1) :=
      (Nat.one_le_iff_ne_zero).2 (pow_ne_zero _ (by norm_num))
    have heq : ((((2 ^ (k + 1) - 1 : ℕ) : ℤ) + 1 - (2 ^ k : ℕ))) =
        ((2 ^ k : ℕ) : ℤ) := by
      rw [Nat.cast_sub hp, pow_succ]
      push_cast
      ring
    rw [heq, Int.toNat_natCast]
  · rw [Int.card_Icc]
    have heq : (((N / 2 ^ k : ℕ) : ℤ) + 1 - (2 ^ l : ℕ)) =
        ((N / 2 ^ k - 2 ^ l + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub hl]
      push_cast
      ring
    rw [heq, Int.toNat_natCast]

/-- The rank-one term is bounded by the honest explicit weak-large-sieve
majorant after scalarizing both coefficient energies. -/
theorem vaughanTypeIIRectangular_rankOneRectangularLSRHS_le_Rexp
    (N u v k l Q : ℕ) (hQ : 0 < Q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    rankOneRectangularLSRHS
        (vaughanTypeIIRectLeftCoeff N u k)
        (vaughanTypeIIRectRightCoeff N v l)
        ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
        (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) Q ≤
      vaughanTypeIIRectangularRexp N k l Q := by
  have hleft := vaughanTypeIIRectLeftCoeff_energy_le N u k
  have hright := vaughanTypeIIRectRightCoeff_energy_le N v k l
  have hdelta : 0 < (1 / (Q : ℝ) ^ 2) := by positivity
  have hCD : 0 ≤ largeSieveBound (2 ^ k) (1 / (Q : ℝ) ^ 2) :=
    largeSieveBound_nonneg _ hdelta
  have hCT : 0 ≤ largeSieveBound (N / 2 ^ k - 2 ^ l + 1)
      (1 / (Q : ℝ) ^ 2) := largeSieveBound_nonneg _ hdelta
  unfold rankOneRectangularLSRHS vaughanTypeIIRectangularRexp
    vaughanTypeIIRectangularD vaughanTypeIIRectangularT
    vaughanTypeIIRectangularEright vaughanTypeIIRectangularX
  rw [show (2 ^ k : ℤ) - 1 + 1 = ((2 ^ k : ℕ) : ℤ) by norm_num,
    left_upper_endpoint k,
    show (2 ^ l : ℤ) - 1 + 1 = ((2 ^ l : ℕ) : ℤ) by norm_num,
    right_upper_endpoint N u v k l hactive]
  apply mul_le_mul
  · apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ hCD
    simpa [Complex.normSq_eq_norm_sq] using hleft
  · apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ hCT
    simpa [Complex.normSq_eq_norm_sq] using hright
  · positivity
  · positivity

/-- The literal rectangular coefficient mass is bounded by the displayed
Cauchy--Schwarz majorant. -/
theorem vaughanTypeIIRectangular_rectangularCoefficientL1_le_L1exp
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    rectangularCoefficientL1
        (vaughanTypeIIRectLeftCoeff N u k)
        (vaughanTypeIIRectRightCoeff N v l)
        ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
        (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) ≤
      vaughanTypeIIRectangularL1exp N k l := by
  let A : ℝ := ∑ m ∈ Finset.Icc ((2 ^ k : ℕ) : ℤ)
      (((2 ^ (k + 1) - 1 : ℕ) : ℤ)), ‖vaughanTypeIIRectLeftCoeff N u k m‖
  let B : ℝ := ∑ n ∈ Finset.Icc ((2 ^ l : ℕ) : ℤ)
      ((N / 2 ^ k : ℕ) : ℤ),
      ‖vaughanTypeIIRectRightCoeff N v l n‖
  have hcards := rectangular_cards N u v k l hactive
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hAsq := finite_norm_sum_sq_le_card_mul_energy
    (Finset.Icc ((2 ^ k : ℕ) : ℤ) (((2 ^ (k + 1) - 1 : ℕ) : ℤ)))
    (vaughanTypeIIRectLeftCoeff N u k)
  have hBsq := finite_norm_sum_sq_le_card_mul_energy
    (Finset.Icc ((2 ^ l : ℕ) : ℤ) ((N / 2 ^ k : ℕ) : ℤ))
    (vaughanTypeIIRectRightCoeff N v l)
  rw [hcards.1] at hAsq
  rw [hcards.2] at hBsq
  have hleft := vaughanTypeIIRectLeftCoeff_energy_le N u k
  have hright := vaughanTypeIIRectRightCoeff_energy_le N v k l
  have hAle : A ≤ Real.sqrt (((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    exact hAsq.trans (mul_le_mul_of_nonneg_left hleft (by positivity))
  have hBle : B ≤ Real.sqrt (((N / 2 ^ k - 2 ^ l + 1 : ℕ) : ℝ) *
      vaughanTypeIIRectangularEright N k) := by
    apply Real.le_sqrt_of_sq_le
    exact hBsq.trans (mul_le_mul_of_nonneg_left hright (by positivity))
  unfold rectangularCoefficientL1 vaughanTypeIIRectangularL1exp
    vaughanTypeIIRectangularD vaughanTypeIIRectangularT
  rw [show (2 ^ k : ℤ) - 1 + 1 = ((2 ^ k : ℕ) : ℤ) by norm_num,
    left_upper_endpoint k,
    show (2 ^ l : ℤ) - 1 + 1 = ((2 ^ l : ℕ) : ℤ) by norm_num,
    right_upper_endpoint N u v k l hactive]
  change A * B ≤ _
  exact mul_le_mul hAle hBle hB0 (Real.sqrt_nonneg _)

/-- Fully explicit honest actual-shell estimate. -/
theorem vaughanActualCanonicalCollectedShellWeightedMean_le_explicit
    (N Q u v k l : ℕ) (hN : 3 ≤ N) (hQ : 0 < Q)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanActualCanonicalCollectedShellWeightedMean N u v k l S ≤
      (1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) *
        vaughanTypeIIRectangularRexp N k l Q +
      (8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
        vaughanTypeIIRectangularL1exp N k l * weightedPrimitiveFamilyMass S := by
  calc
    vaughanActualCanonicalCollectedShellWeightedMean N u v k l S ≤
        (1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) *
          rankOneRectangularLSRHS
            (vaughanTypeIIRectLeftCoeff N u k)
            (vaughanTypeIIRectRightCoeff N v l)
            ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
            (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) Q +
        (8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
          rectangularCoefficientL1
            (vaughanTypeIIRectLeftCoeff N u k)
            (vaughanTypeIIRectRightCoeff N v l)
            ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
            (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) * weightedPrimitiveFamilyMass S :=
      vaughanActualCanonicalCollectedShellWeightedMean_le N Q u v k l hN hQ S hS hactive
    _ ≤ _ := by
      have hR := vaughanTypeIIRectangular_rankOneRectangularLSRHS_le_Rexp
        N u v k l Q hQ hactive
      have hL := vaughanTypeIIRectangular_rectangularCoefficientL1_le_L1exp
        N u v k l hactive
      have hdamp : 0 ≤
          (1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) := by
        have hlog : 0 ≤ Real.log ((2 * N : ℕ) : ℝ) := by
          apply Real.log_nonneg
          exact_mod_cast (show 1 ≤ 2 * N by omega)
        positivity
      have herr : 0 ≤ 8 / (Real.pi * ((2 * N : ℕ) : ℝ)) := by positivity
      have hmass : 0 ≤ weightedPrimitiveFamilyMass S := by
        unfold weightedPrimitiveFamilyMass
        positivity
      gcongr

end
end AnalyticNumberTheory.LargeSieve

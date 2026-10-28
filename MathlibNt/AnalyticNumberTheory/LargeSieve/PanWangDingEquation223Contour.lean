import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingEarlySourceReduction
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21FiniteContour

set_option maxHeartbeats 800000
noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-! ## Source coefficients and the literal kernel -/

/-- Equation (2.8), with the original coprimality restriction. -/
def panSourceG (f : ℕ → ℂ) (m n : ℕ) : ℂ :=
  if Nat.Coprime n m then f n else 0

/-- Equations (2.2), (2.8): the prime indicator restricted by `(n,m)=1`. -/
def panSourceD (m n : ℕ) : ℂ :=
  if Nat.Coprime n m ∧ Nat.Prime n then 1 else 0

/-- The literal short polynomial (2.19). -/
def panShortF₁ {q : ℕ} (m H : ℕ) (χ : PrimitiveCharacter q) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 H, panSourceD m n * χ.1 (n : ZMod q) / (n : ℂ) ^ s

/-- Equation (2.21), including the clipped last dyadic cell. -/
def panDyadicG {q : ℕ} (f : ℕ → ℂ) (m A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) (s : ℂ) : ℂ :=
  ∑ a ∈ Finset.Ioc (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂),
    panSourceG f m a * χ.1 (a : ZMod q) / (a : ℂ) ^ s


/-! ## Analyticity and the oriented rectangle identity -/

theorem panFinitePolynomial_differentiable (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) :
    Differentiable ℂ (fun s : ℂ => ∑ n ∈ S, c n / (n : ℂ) ^ s) := by
  apply Differentiable.fun_sum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (hS n hn).ne'
  exact (differentiable_const _).div
    (differentiable_id.const_cpow (Or.inl hn0))
    (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))

theorem panShortF₁_differentiable {q : ℕ} (m H : ℕ) (χ : PrimitiveCharacter q) :
    Differentiable ℂ (panShortF₁ m H χ) := by
  apply panFinitePolynomial_differentiable
  intro n hn
  exact (Finset.mem_Icc.mp hn).1

theorem panDyadicG_differentiable {q : ℕ} (f : ℕ → ℂ) (m A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) : Differentiable ℂ (panDyadicG f m A₁ A₂ k χ) := by
  apply panFinitePolynomial_differentiable
  intro a ha
  exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp ha).1


/-! ## Coefficient, half-sum, and horizontal pointwise bounds -/

theorem panSourceG_norm_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (m n : ℕ) :
    ‖panSourceG f m n‖ ≤ 1 := by
  unfold panSourceG
  split_ifs <;> simp [hf]

theorem panSourceD_norm_le (m n : ℕ) : ‖panSourceD m n‖ ≤ 1 := by
  unfold panSourceD
  split_ifs <;> norm_num

/-- The precise reciprocal-square-root sum in (2.23). -/
def panHalfSum (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (Real.sqrt n)⁻¹


theorem panHalfSum_nonneg (N : ℕ) : 0 ≤ panHalfSum N := by
  unfold panHalfSum
  positivity

theorem panFinitePolynomial_norm_le (S : Finset ℕ) (c : ℕ → ℂ)
    (N : ℕ) (hS : S ⊆ Finset.Icc 1 N) (hc : ∀ n ∈ S, ‖c n‖ ≤ 1)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖∑ n ∈ S, c n / (n : ℂ) ^ s‖ ≤ panHalfSum N := by
  calc
    _ ≤ ∑ n ∈ S, ‖c n / (n : ℂ) ^ s‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, (Real.sqrt n)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp (hS hn)).1
      have hn0 : (0 : ℝ) < n := by linarith
      rw [norm_div, show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      calc
        ‖c n‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right (hc n hn) (Real.rpow_nonneg hn0.le _)
        _ ≤ 1 / Real.sqrt n := by
          apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hn0)
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le hn1 hs
        _ = _ := one_div _
    _ ≤ panHalfSum N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro n _ _
      positivity

theorem panShortF₁_norm_le {q : ℕ} (m H : ℕ) (χ : PrimitiveCharacter q)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) : ‖panShortF₁ m H χ s‖ ≤ panHalfSum H := by
  apply panFinitePolynomial_norm_le _ _ H (fun _ h => h) _ s hs
  intro n _
  rw [norm_mul]
  exact mul_le_one₀ (panSourceD_norm_le m n) (norm_nonneg _) (χ.1.norm_le_one _)

theorem panDyadicG_norm_le {q : ℕ} (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (m A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) : ‖panDyadicG f m A₁ A₂ k χ s‖ ≤ panHalfSum A₂ := by
  apply panFinitePolynomial_norm_le _ _ A₂ _ _ s hs
  · intro a ha
    rcases Finset.mem_Ioc.mp ha with ⟨ha, hb⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hb.trans (min_le_right _ _)⟩
  · intro a _
    rw [norm_mul]
    exact mul_le_one₀ (panSourceG_norm_le f hf m a) (norm_nonneg _) (χ.1.norm_le_one _)


/-! ## Integrability and the finite-shift estimate -/


end AnalyticNumberTheory.LargeSieve
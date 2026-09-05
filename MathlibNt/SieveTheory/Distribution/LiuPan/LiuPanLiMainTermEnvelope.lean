import MathlibNt.SieveTheory.Arithmetic.LiuLogarithmicIntegral
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanAggregatePsiCharacters
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969Ordinary418Specialization

/-! Pointwise envelopes for the literal Liu main term. The additive
normalization κ is unrestricted; no distribution hypothesis is introduced. -/

noncomputable section
open Finset
open scoped BigOperators
namespace MathlibNt.SieveTheory.LiuWeight

/-- Nonzero Liu weight forces a positive supported index and a real quotient ≥ 2. -/
theorem liuWeight_ne_zero_index_and_quotient {N z y a : ℕ}
    (ha : liuWeight N z y a ≠ 0) :
    1 ≤ a ∧ a ≤ N ∧ 2 ≤ (N : ℝ) / a := by
  have hs : LiuWeightSupport N z y a := by
    by_contra h
    exact ha (liuWeight_eq_zero_iff.mpr h)
  have haN := liuWeightSupport_le hs
  rcases liuWeightSupport_iff.mp hs with ⟨p₁, p₂, hp, rfl⟩
  have hp₁ := hp.1.pos
  have hp₂ := hp.2.1.two_le
  have hpos : 0 < p₁ * p₂ := Nat.mul_pos hp₁ (by omega)
  refine ⟨hpos, haN, ?_⟩
  have hsize : 2 * (p₁ * p₂) ≤ N := calc
    2 * (p₁ * p₂) ≤ p₂ * (p₁ * p₂) := Nat.mul_le_mul_right _ hp₂
    _ = p₁ * p₂ ^ 2 := by ring
    _ ≤ N := hp.2.2.2.2.2
  apply (le_div_iff₀ (show (0 : ℝ) < (p₁ * p₂ : ℕ) by exact_mod_cast hpos)).mpr
  exact_mod_cast hsize

/-- The fixed coefficient costs only the lower endpoint log 2. -/
def liuPanLiEnvelopeConstant (κ : ℝ) : ℝ :=
  liuLogarithmicIntegralUpperConstant κ / Real.log 2

theorem liuPanLiEnvelopeConstant_pos (κ : ℝ) :
    0 < liuPanLiEnvelopeConstant κ := by
  unfold liuPanLiEnvelopeConstant liuLogarithmicIntegralUpperConstant
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

theorem liuPanLiEnvelopeConstant_nonneg (κ : ℝ) :
    0 ≤ liuPanLiEnvelopeConstant κ :=
  div_nonneg (liuLogarithmicIntegralUpperConstant_nonneg κ)
    (Real.log_nonneg (by norm_num))

/-- The genuine integral is evaluated only on its supported domain. -/
theorem abs_liuWeight_mul_logarithmicIntegral_le (κ : ℝ) (N z y a : ℕ) :
    |liuWeight N z y a * liuLogarithmicIntegral κ ((N : ℝ) / a)| ≤
      (liuPanLiEnvelopeConstant κ * N) * (liuWeight N z y a / a) := by
  by_cases ha : liuWeight N z y a = 0
  · simp [ha]
  have hquot := (liuWeight_ne_zero_index_and_quotient ha).2.2
  have hx0 : 0 ≤ (N : ℝ) / a := by positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log (2 : ℝ) ≤ Real.log ((N : ℝ) / a) :=
    Real.log_le_log (by norm_num) hquot
  have hLi : |liuLogarithmicIntegral κ ((N : ℝ) / a)| ≤
      liuPanLiEnvelopeConstant κ * ((N : ℝ) / a) := calc
    _ ≤ liuLogarithmicIntegralUpperConstant κ * ((N : ℝ) / a) /
        Real.log ((N : ℝ) / a) := liuLogarithmicIntegral_abs_le κ hquot
    _ ≤ liuLogarithmicIntegralUpperConstant κ * ((N : ℝ) / a) /
        Real.log 2 :=
      div_le_div_of_nonneg_left
        (mul_nonneg (liuLogarithmicIntegralUpperConstant_nonneg κ) hx0) hlog2 hlog
    _ = _ := by unfold liuPanLiEnvelopeConstant; ring
  rw [abs_mul, abs_liuWeight]
  calc
    _ ≤ liuWeight N z y a * (liuPanLiEnvelopeConstant κ * ((N : ℝ) / a)) :=
      mul_le_mul_of_nonneg_left hLi (liuWeight_nonneg N z y a)
    _ = _ := by ring

/-- Any finite window can be enlarged to the mother sum, even above N. -/
theorem sum_liuWeight_div_finset_le_one_add_log (N : ℕ) (S : Finset ℕ) :
    ∑ a ∈ S, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a ≤
      1 + Real.log N := by
  let w := liuWeight N (liuSourceZ10 N) (liuSourceY3 N)
  have htrunc : ∑ a ∈ S ∩ Icc 1 N, w a / a = ∑ a ∈ S, w a / a := by
    apply sum_subset inter_subset_left
    intro a ha hnot
    have hw : w a = 0 := by
      by_contra hw
      have hs := liuWeight_ne_zero_index_and_quotient hw
      exact hnot (mem_inter.mpr ⟨ha, mem_Icc.mpr ⟨hs.1, hs.2.1⟩⟩)
    simp [hw]
  calc
    _ = ∑ a ∈ S ∩ Icc 1 N, w a / a := htrunc.symm
    _ ≤ ∑ a ∈ Icc 1 N, w a / a := by
      apply sum_le_sum_of_subset_of_nonneg inter_subset_right
      intro a _ _
      exact div_nonneg (liuWeight_nonneg _ _ _ _) (Nat.cast_nonneg _)
    _ ≤ 1 + Real.log N := sum_liuWeight_div_le_one_add_log N

/-- Whole-sum absolute value, literal genuine Liκ, and original totient divisor. -/
theorem abs_liuPanLi_mainTerm_finset_le (κ : ℝ) (N q : ℕ) (S : Finset ℕ) :
    |∑ a ∈ S, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
        liuLogarithmicIntegral κ ((N : ℝ) / a) / (q.totient : ℝ)| ≤
      liuPanLiEnvelopeConstant κ * N * (1 + Real.log N) / q.totient := by
  calc
    _ ≤ ∑ a ∈ S, |liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
        liuLogarithmicIntegral κ ((N : ℝ) / a) / (q.totient : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ S, ((liuPanLiEnvelopeConstant κ * N) *
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a)) / q.totient := by
      apply sum_le_sum
      intro a _
      rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (q.totient : ℝ) from Nat.cast_nonneg _)]
      exact div_le_div_of_nonneg_right
        (abs_liuWeight_mul_logarithmicIntegral_le κ N _ _ a) (Nat.cast_nonneg _)
    _ = ((liuPanLiEnvelopeConstant κ * N) *
        (∑ a ∈ S, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a)) /
          q.totient := by rw [← sum_div, ← mul_sum]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (sum_liuWeight_div_finset_le_one_add_log N S)
        (mul_nonneg (liuPanLiEnvelopeConstant_nonneg κ) (Nat.cast_nonneg _))

/-- Uniform interval version, with no upper restriction on A₂. -/
theorem abs_liuPanLi_mainTerm_Ioc_le (κ : ℝ) (N q A₁ A₂ : ℕ) :
    |∑ a ∈ (Ioc A₁ A₂).filter (fun a => a.Coprime q),
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          liuLogarithmicIntegral κ ((N : ℝ) / a) / (q.totient : ℝ)| ≤
      liuPanLiEnvelopeConstant κ * N * (1 + Real.log N) / q.totient :=
  abs_liuPanLi_mainTerm_finset_le κ N q _

/-- The constant is selected before all endpoints and moduli. -/
theorem exists_abs_liuPanLi_mainTerm_Ioc_le (κ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N q A₁ A₂ : ℕ, 2 ≤ N → 0 < q →
      |∑ a ∈ (Ioc A₁ A₂).filter (fun a => a.Coprime q),
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
            liuLogarithmicIntegral κ ((N : ℝ) / a) / (q.totient : ℝ)| ≤
        C * N * (1 + Real.log N) / q.totient :=
  ⟨liuPanLiEnvelopeConstant κ, liuPanLiEnvelopeConstant_pos κ,
    fun N q A₁ A₂ _ _ => abs_liuPanLi_mainTerm_Ioc_le κ N q A₁ A₂⟩

/-- The extra reciprocal-totient payment is independent of N, q and the window. -/
def liuPanLiModulusEnvelopeConstant (κ : ℝ) : ℝ :=
  liuPanLiEnvelopeConstant κ * Richert1969.richertReciprocalTotientConstant

theorem liuPanLiModulusEnvelopeConstant_pos (κ : ℝ) :
    0 < liuPanLiModulusEnvelopeConstant κ :=
  mul_pos (liuPanLiEnvelopeConstant_pos κ) Richert1969.richertReciprocalTotientConstant_pos

/-- Multiplication by q costs at most a second logarithm for 0 < q ≤ N. -/
theorem modulus_mul_abs_liuPanLi_mainTerm_finset_le (κ : ℝ)
    {N q : ℕ} (hN : 2 ≤ N) (hq : 0 < q) (hqN : q ≤ N) (S : Finset ℕ) :
    (q : ℝ) * |∑ a ∈ S,
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          liuLogarithmicIntegral κ ((N : ℝ) / a) / (q.totient : ℝ)| ≤
      liuPanLiModulusEnvelopeConstant κ * N * (1 + Real.log N) ^ 2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hC := liuPanLiEnvelopeConstant_nonneg κ
  have hD := Richert1969.richertReciprocalTotientConstant_pos.le
  have hphi := Richert1969.reciprocal_totient_le_richertConstant_log_div hN hq hqN
  have hratio : (q : ℝ) / q.totient ≤
      Richert1969.richertReciprocalTotientConstant * Real.log N := by
    have h := mul_le_mul_of_nonneg_left hphi hqR.le
    calc
      (q : ℝ) / q.totient = q * (1 / (q.totient : ℝ)) := by ring
      _ ≤ q * (Richert1969.richertReciprocalTotientConstant * Real.log N / q) := h
      _ = _ := by field_simp
  have hbase : 0 ≤ liuPanLiEnvelopeConstant κ * (N : ℝ) * (1 + Real.log N) := by
    positivity
  calc
    _ ≤ (q : ℝ) * (liuPanLiEnvelopeConstant κ * N * (1 + Real.log N) / q.totient) :=
      mul_le_mul_of_nonneg_left (abs_liuPanLi_mainTerm_finset_le κ N q S) hqR.le
    _ = (liuPanLiEnvelopeConstant κ * N * (1 + Real.log N)) *
        ((q : ℝ) / q.totient) := by ring
    _ ≤ (liuPanLiEnvelopeConstant κ * N * (1 + Real.log N)) *
        (Richert1969.richertReciprocalTotientConstant * Real.log N) :=
      mul_le_mul_of_nonneg_left hratio hbase
    _ ≤ (liuPanLiEnvelopeConstant κ * N * (1 + Real.log N)) *
        (Richert1969.richertReciprocalTotientConstant * (1 + Real.log N)) := by
      apply mul_le_mul_of_nonneg_left _ hbase
      exact mul_le_mul_of_nonneg_left (by linarith) hD
    _ = _ := by unfold liuPanLiModulusEnvelopeConstant; ring

/-- Coprime interval specialization, still with no upper restriction on A₂. -/
theorem modulus_mul_abs_liuPanLi_mainTerm_Ioc_le (κ : ℝ)
    {N q : ℕ} (hN : 2 ≤ N) (hq : 0 < q) (hqN : q ≤ N) (A₁ A₂ : ℕ) :
    (q : ℝ) * |∑ a ∈ (Ioc A₁ A₂).filter (fun a => a.Coprime q),
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          liuLogarithmicIntegral κ ((N : ℝ) / a) / (q.totient : ℝ)| ≤
      liuPanLiModulusEnvelopeConstant κ * N * (1 + Real.log N) ^ 2 :=
  modulus_mul_abs_liuPanLi_mainTerm_finset_le κ hN hq hqN _

/-- Quantifier order suitable for the later actual interval-maximal error bound. -/
theorem exists_modulus_mul_abs_liuPanLi_mainTerm_Ioc_le (κ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N q A₁ A₂ : ℕ, 2 ≤ N → 0 < q → q ≤ N →
      (q : ℝ) * |∑ a ∈ (Ioc A₁ A₂).filter (fun a => a.Coprime q),
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
            liuLogarithmicIntegral κ ((N : ℝ) / a) / (q.totient : ℝ)| ≤
        C * N * (1 + Real.log N) ^ 2 :=
  ⟨liuPanLiModulusEnvelopeConstant κ, liuPanLiModulusEnvelopeConstant_pos κ,
    fun _ _ A₁ A₂ hN hq hqN => modulus_mul_abs_liuPanLi_mainTerm_Ioc_le κ hN hq hqN A₁ A₂⟩

end MathlibNt.SieveTheory.LiuWeight
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryZeroModeBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmallDeltaPayment

/-!
# Family-uniform logarithmic payment of the complete zero-mode difference

The SW input is the existing all-positive-modulus, coprime-sieved family
condition. Constants precede all family members, supports, scales, modulus
weights and integer residues. The lcm-weight estimate leaves no gcd range
unpaid in W zero minus U zero. Nonzero W frequencies are not estimated here.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset Filter
open scoped Topology

noncomputable section

theorem smoothWMain_sub_smoothUMain_abs_le_SW
    {k : ℕ} (hk : 1 ≤ k) (j κ B : ℕ)
    {T L C : ℝ} (hT : 1 ≤ T) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (M : ℝ) (N Q : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊)
    (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) (β c : ℕ → ℝ)
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ)
    (hSW : ∀ d h : ℕ, 0 < d → 0 < h → ∀ b : ℕ, b.Coprime d →
      |betaCoprimeAPDiscrepancy N β d h b| ≤
        C * T * (fouvryTau κ h : ℝ) / Real.log (2 * T) ^ B) :
    |smoothWMain M N Q β c a - smoothUMain M N Q β c a| ≤
      2 * |M * dyadicCutoffMass| * C * T ^ 2 *
        ((1 + Real.log T) ^ (k - 1) *
          (1 + Real.log L) ^ (2 * (j * (κ + 1)) ^ 2 + 1) /
            Real.log (2 * T) ^ B) := by
  have hlog : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  have h := smoothWMain_sub_smoothUMain_abs_le_coprimeAP_lcm hk j κ hT hL
    (show 0 ≤ C * T / Real.log (2 * T) ^ B by positivity)
    M N Q hN hQ β c hβ hc a ?_
  · exact h.trans_eq (by ring)
  · intro q hq δ hdq hδ b hb
    have hq0 := (mem_Ioc.mp (hQ hq)).1
    have hsieve : 0 < q / δ := Nat.div_pos (Nat.le_of_dvd hq0 hdq) hδ
    exact (hSW δ (q / δ) hδ hsieve b (mem_filter.mp hb).2).trans_eq (by ring)

/-- All gcd ranges are paid in the natural `|M| T^2` normalization, with
the threshold chosen before every family member and arithmetic parameter. -/
theorem smoothWU_SWFamily_log_payment
    {ι : Type*} {κ k : ℕ} (hk : 1 ≤ k) (j A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β)
    (hT : ∀ i, 1 ≤ T i) (hN : ∀ i, N i ⊆ Ioc 0 ⌊T i⌋₊)
    (hβ : ∀ i, ∀ n ∈ N i, |β i n| ≤ (fouvryTau k n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ i : ι, T i ≤ x → x ^ ε ≤ T i →
      ∀ M L : ℝ, 1 ≤ L → L ≤ x →
      ∀ Q : Finset ℕ, Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ,
        |smoothWMain M (N i) Q (β i) c a - smoothUMain M (N i) Q (β i) c a| ≤
          |M| * T i ^ 2 / Real.log x ^ A := by
  let p := k - 1
  let s := 2 * (j * (κ + 1)) ^ 2 + 1
  let B := (A + 1) + (p + s)
  obtain ⟨C, hC, hAP⟩ := hSW B
  let K := 2 * |dyadicCutoffMass| * C * ((2 : ℝ) ^ (p + s) / ε ^ B)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 K)] with x hx hxlog
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := (le_max_left _ _).trans hxlog
  have hlogK : K ≤ Real.log x := (le_max_right _ _).trans hxlog
  have hlog0 : 0 < Real.log x := by linarith
  intro i hTx hεT M L hL hLx Q hQ c hc a
  have hb := smoothWMain_sub_smoothUMain_abs_le_SW hk j κ B (hT i) hL hC.le
    M (N i) Q (hN i) hQ (β i) c (hβ i) hc a (hAP i)
  have hbudget :
      (1 + Real.log (T i)) ^ p * (1 + Real.log L) ^ s /
          Real.log (2 * T i) ^ B ≤
        (2 : ℝ) ^ (p + s) / ε ^ B / Real.log x ^ (A + 1) := by
    simpa only [Nat.add_zero, mul_one] using
      smallDelta_log_budget p s 0 (A + 1)
        hlog1 hx0 (hT i) hL hTx hLx hε hεT
        (D := 1) zero_le_one (by simp)
  calc
    _ ≤ 2 * |M * dyadicCutoffMass| * C * T i ^ 2 *
        ((2 : ℝ) ^ (p + s) / ε ^ B / Real.log x ^ (A + 1)) :=
      hb.trans (mul_le_mul_of_nonneg_left hbudget (by positivity))
    _ = (|M| * T i ^ 2 / Real.log x ^ A) * (K / Real.log x) := by
      dsimp [K]
      rw [abs_mul, pow_succ]
      ring
    _ ≤ (|M| * T i ^ 2 / Real.log x ^ A) * 1 :=
      mul_le_mul_of_nonneg_left ((div_le_one hlog0).mpr hlogK) (by positivity)
    _ = _ := mul_one _

/-- Actual alpha second moment times the full W-zero-minus-U-zero difference
is `O(x^2 log(x)^(-A))`. No large-gcd subtraction or unestimated covariance
term remains, and the residue may be any varying signed integer. -/
theorem alpha_sq_mul_smoothWU_SWFamily_log_payment
    {ι : Type*} {κ k ℓ : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (j A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β)
    (hT : ∀ i, 1 ≤ T i) (hN : ∀ i, N i ⊆ Ioc 0 ⌊T i⌋₊)
    (hβ : ∀ i, ∀ n ∈ N i, |β i n| ≤ (fouvryTau k n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ i : ι, ∀ M L : ℝ,
      1 ≤ M → 1 ≤ L → M * T i ≤ x → L ≤ x → x ^ ε ≤ T i →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau ℓ m : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) → ∀ a : ℤ,
      (∑ m ∈ S, α m ^ 2) *
        |smoothWMain M (N i) Q (β i) c a - smoothUMain M (N i) Q (β i) c a| ≤
        x ^ 2 / Real.log x ^ A := by
  let u := ℓ ^ 2 - 1
  filter_upwards [smoothWU_SWFamily_log_payment hk j (A + u + 1)
    hSW hT hN hβ hε, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (2 * (3 : ℝ) ^ u))]
      with x hzero hx hxlog
  have hlog1 : 1 ≤ Real.log x := (le_max_left _ _).trans hxlog
  have hlogC : 2 * (3 : ℝ) ^ u ≤ Real.log x := (le_max_right _ _).trans hxlog
  have hlog0 : 0 < Real.log x := by linarith
  intro i M L hM hL hMT hLx hεT S Q hS hQ α c hα hc a
  have hM0 : 0 ≤ M := by linarith
  have hTi0 : 0 ≤ T i := by linarith [hT i]
  have hMx : M ≤ x := (le_mul_of_one_le_right hM0 (hT i)).trans hMT
  have hTx : T i ≤ x := (le_mul_of_one_le_left hTi0 hM).trans hMT
  have hzero' := hzero i hTx hεT M L hL hLx Q hQ c hc a
  rw [abs_of_nonneg hM0] at hzero'
  have hH : 1 + Real.log (2 * M) ≤ 3 * Real.log x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : M ≠ 0)]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    have := Real.log_le_log (by linarith : 0 < M) hMx
    linarith
  have hA : (∑ m ∈ S, α m ^ 2) ≤ 2 * M * (3 * Real.log x) ^ u := by
    apply (sum_alpha_sq_dyadic_le hℓ hM S hS α hα).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀
      (by have := Real.log_nonneg (show 1 ≤ 2 * M by linarith); positivity) hH _
  calc
    _ ≤ (2 * M * (3 * Real.log x) ^ u) *
        (M * T i ^ 2 / Real.log x ^ (A + u + 1)) :=
      mul_le_mul hA hzero' (abs_nonneg _) (by positivity)
    _ = (M * T i) ^ 2 / Real.log x ^ A * (2 * (3 : ℝ) ^ u / Real.log x) := by
      simp only [mul_pow, pow_add, pow_one]
      field_simp
    _ ≤ (x ^ 2 / Real.log x ^ A) * 1 := by
      apply mul_le_mul
      · apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (mul_nonneg hM0 hTi0) hMT _
      · exact (div_le_one hlog0).mpr hlogC
      · positivity
      · positivity
    _ = _ := mul_one _

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

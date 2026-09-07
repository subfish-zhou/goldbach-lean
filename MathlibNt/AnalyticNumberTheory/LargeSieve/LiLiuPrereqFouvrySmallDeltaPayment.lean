import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmallDelta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform logarithmic payment of the small-gcd zero-mode difference

Siegel--Walfisz is a hypothesis on a given family, not a property asserted
for arbitrary beta. Its constant is chosen before the family member and all
AP moduli, coprime sieves, and residues. The threshold below is likewise
chosen before the member, scales, supports, and signed modulus weights.
The large-gcd term remains outside these estimates.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset Filter
open scoped Topology

noncomputable section

/-- The family-uniform, independently coprime-sieved beta-SW input.
The sieve order is fixed; the saving exponent and its constant precede
every changing family member and every arithmetic parameter. -/
def BetaCoprimeSWFamily {ι : Type*} (κ : ℕ) (T : ι → ℝ)
    (N : ι → Finset ℕ) (β : ι → ℕ → ℝ) : Prop :=
  ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ i : ι, ∀ d h : ℕ, 0 < d → 0 < h → ∀ b : ℕ, b.Coprime d →
      |betaCoprimeAPDiscrepancy (N i) (β i) d h b| ≤
        C * T i * (fouvryTau κ h : ℝ) / Real.log (2 * T i) ^ B

/-- Passing from the lower dyadic scale to the upper support endpoint does
not strengthen the SW input: its constant grows by the fixed factor `2^B`. -/
theorem BetaCoprimeSWFamily.double_scale
    {ι : Type*} {κ : ℕ} {T : ι → ℝ}
    {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ i, 1 ≤ T i) :
    BetaCoprimeSWFamily κ (fun i => 2 * T i) N β := by
  intro B
  obtain ⟨C, hC, hAP⟩ := hSW B
  refine ⟨C * 2 ^ B, by positivity, ?_⟩
  intro i d h hd hh b hb
  have ht : 0 < T i := lt_of_lt_of_le zero_lt_one (hT i)
  have hl : 0 < Real.log (2 * T i) := Real.log_pos (by linarith [hT i])
  have hl' : 0 < Real.log (2 * (2 * T i)) := Real.log_pos (by linarith [hT i])
  have hlog : Real.log (2 * (2 * T i)) ≤ 2 * Real.log (2 * T i) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 * T i ≠ 0)]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show 2 ≤ 2 * T i by linarith [hT i])
    linarith
  have hp := pow_le_pow_left₀ hl'.le hlog B
  rw [mul_pow] at hp
  apply (hAP i d h hd hh b hb).trans
  apply (div_le_div_iff₀ (pow_pos hl B) (pow_pos hl' B)).mpr
  calc
    _ ≤ (C * T i * (fouvryTau κ h : ℝ)) * (2 ^ B * Real.log (2 * T i) ^ B) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := by
      have hn : 0 ≤ C * T i * (fouvryTau κ h : ℝ) *
          (2 ^ B * Real.log (2 * T i) ^ B) := by positivity
      nlinarith

/-- The explicit SW small-gcd bound, retaining the original sieve order. -/
theorem smoothWUSmallDelta_abs_le_SW
    {k : ℕ} (hk : 1 ≤ k) (j κ B : ℕ)
    {T L D C : ℝ} (hT : 1 ≤ T) (hL : 1 ≤ L) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (M : ℝ) (N Q : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (β c : ℕ → ℝ) (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ)
    (hSW : ∀ d h : ℕ, 0 < d → 0 < h → ∀ b : ℕ, b.Coprime d →
      |betaCoprimeAPDiscrepancy N β d h b| ≤
        C * T * (fouvryTau κ h : ℝ) / Real.log (2 * T) ^ B) :
    |smoothWUSmallDelta M D N Q β c a| ≤
      2 * |M * dyadicCutoffMass| * C * T ^ 2 *
        ((1 + Real.log T) ^ (k - 1) * D *
          (1 + Real.log L) ^ (j * (κ + 2)) / Real.log (2 * T) ^ B) := by
  have hlog : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  have h := smoothWUSmallDelta_abs_le hk j κ hT hL hD
    (show 0 ≤ C * T / Real.log (2 * T) ^ B by positivity)
    M N Q hN hQ β c hβ hc a ?_
  · exact h.trans_eq (by ring)
  · intro q hq δ hdq hδ _ b hb
    have hq0 := (mem_Ioc.mp (hQ hq)).1
    have hsieve : 0 < q / δ :=
      Nat.div_pos (Nat.le_of_dvd hq0 hdq) hδ
    exact (hSW δ (q / δ) hδ hsieve b (mem_filter.mp hb).2).trans_eq (by ring)

/-- Elementary logarithm accounting at `T ≥ x^ε`. The saving order is
explicitly the desired order plus the beta/modulus/delta logarithm costs. -/
theorem smallDelta_log_budget (p s d A : ℕ)
    {x T L D ε : ℝ} (hx : 1 ≤ Real.log x) (hx0 : 0 < x)
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hTx : T ≤ x) (hLx : L ≤ x)
    (hε : 0 < ε) (hεT : x ^ ε ≤ T) (hD : 0 ≤ D)
    (hDx : D ≤ Real.log x ^ d) :
    (1 + Real.log T) ^ p * D * (1 + Real.log L) ^ s /
        Real.log (2 * T) ^ (A + (p + s + d)) ≤
      (2 : ℝ) ^ (p + s) / ε ^ (A + (p + s + d)) / Real.log x ^ A := by
  have hlogx : 0 < Real.log x := by linarith
  have hlogT := Real.log_nonneg hT
  have hlogL := Real.log_nonneg hL
  have hHT : 1 + Real.log T ≤ 2 * Real.log x := by
    have := Real.log_le_log (by linarith : 0 < T) hTx
    linarith
  have hHL : 1 + Real.log L ≤ 2 * Real.log x := by
    have := Real.log_le_log (by linarith : 0 < L) hLx
    linarith
  have hden : ε * Real.log x ≤ Real.log (2 * T) := by
    have h₁ := Real.log_le_log (Real.rpow_pos_of_pos hx0 ε) hεT
    rw [Real.log_rpow hx0] at h₁
    have h₂ := Real.log_le_log (by linarith : 0 < T) (show T ≤ 2 * T by linarith)
    linarith
  have hden0 : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  calc
    _ ≤ (2 * Real.log x) ^ p * Real.log x ^ d * (2 * Real.log x) ^ s /
        (ε * Real.log x) ^ (A + (p + s + d)) := by
      apply div_le_div₀
      · positivity
      · gcongr
      · positivity
      · exact pow_le_pow_left₀ (by positivity) hden _
    _ = _ := by
      simp only [mul_pow, pow_add]
      field_simp

/-- Genuine uniform log saving for the small-gcd part of W zero minus U zero,
in the natural `|M| T²` normalization. The threshold depends on the given
family SW constants and fixed orders, never on the family member or residue.
No relation between `M` and `x` is needed for this stronger normalized form. -/
theorem smoothWUSmallDelta_SWFamily_log_payment
    {ι : Type*} {κ k : ℕ} (hk : 1 ≤ k) (j d A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β)
    (hT : ∀ i, 1 ≤ T i) (hN : ∀ i, N i ⊆ Ioc 0 ⌊T i⌋₊)
    (hβ : ∀ i, ∀ n ∈ N i, |β i n| ≤ (fouvryTau k n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ i : ι, T i ≤ x → x ^ ε ≤ T i →
      ∀ M L D : ℝ, 1 ≤ L → L ≤ x → 0 ≤ D → D ≤ Real.log x ^ d →
      ∀ Q : Finset ℕ, Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |smoothWUSmallDelta M D (N i) Q (β i) c a| ≤
        |M| * T i ^ 2 / Real.log x ^ A := by
  let p := k - 1
  let s := j * (κ + 2)
  let B := (A + 1) + (p + s + d)
  obtain ⟨C, hC, hAP⟩ := hSW B
  let K := 2 * |dyadicCutoffMass| * C * ((2 : ℝ) ^ (p + s) / ε ^ B)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 K)] with x hx hxlog
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := (le_max_left _ _).trans hxlog
  have hlogK : K ≤ Real.log x := (le_max_right _ _).trans hxlog
  have hlog0 : 0 < Real.log x := by linarith
  intro i hTx hεT M L D hL hLx hD hDx Q hQ c hc a
  have hb := smoothWUSmallDelta_abs_le_SW hk j κ B (hT i) hL hD hC.le
    M (N i) Q (hN i) hQ (β i) c (hβ i) hc a (hAP i)
  have hbudget := smallDelta_log_budget p s d (A + 1)
    hlog1 hx0 (hT i) hL hTx hLx hε hεT hD hDx
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

/-- After the actual alpha second moment, the small-gcd part is paid at
`x² / log(x)^A` whenever `M T ≤ x` and `T ≥ x^ε`. The statement uses the
actual W-minus-U zero modes minus their explicit large-gcd remainder.
It makes no assertion that this remaining large-gcd term is small. -/
theorem alpha_sq_mul_smoothWU_sub_large_SWFamily_log_payment
    {ι : Type*} {κ k ℓ : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (j d A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β)
    (hT : ∀ i, 1 ≤ T i) (hN : ∀ i, N i ⊆ Ioc 0 ⌊T i⌋₊)
    (hβ : ∀ i, ∀ n ∈ N i, |β i n| ≤ (fouvryTau k n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ i : ι, ∀ M L D : ℝ,
      1 ≤ M → 1 ≤ L → M * T i ≤ x → L ≤ x → x ^ ε ≤ T i →
      0 ≤ D → D ≤ Real.log x ^ d →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau ℓ m : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) → ∀ a : ℤ,
      (∑ m ∈ S, α m ^ 2) *
        |smoothWMain M (N i) Q (β i) c a - smoothUMain M (N i) Q (β i) c a -
          smoothWULargeDelta M D (N i) Q (β i) c a| ≤
        x ^ 2 / Real.log x ^ A := by
  let u := ℓ ^ 2 - 1
  filter_upwards [smoothWUSmallDelta_SWFamily_log_payment hk j d (A + u + 1)
    hSW hT hN hβ hε, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (2 * (3 : ℝ) ^ u))]
      with x hsmall hx hxlog
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := (le_max_left _ _).trans hxlog
  have hlogC : 2 * (3 : ℝ) ^ u ≤ Real.log x := (le_max_right _ _).trans hxlog
  have hlog0 : 0 < Real.log x := by linarith
  intro i M L D hM hL hMT hLx hεT hD hDx S Q hS hQ α c hα hc a
  have hM0 : 0 ≤ M := by linarith
  have hTi0 : 0 ≤ T i := by linarith [hT i]
  have hMx : M ≤ x := (le_mul_of_one_le_right hM0 (hT i)).trans hMT
  have hTx : T i ≤ x := (le_mul_of_one_le_left hTi0 hM).trans hMT
  have hsmall' := hsmall i hTx hεT M L D hL hLx hD hDx Q hQ c hc a
  rw [abs_of_nonneg hM0] at hsmall'
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
  rw [smoothWMain_sub_smoothUMain_eq_small_add_large M D (N i) Q (β i) c a
    (fun q hq => (mem_Ioc.mp (hQ hq)).1.ne'), add_sub_cancel_right]
  calc
    _ ≤ (2 * M * (3 * Real.log x) ^ u) *
        (M * T i ^ 2 / Real.log x ^ (A + u + 1)) :=
      mul_le_mul hA hsmall' (abs_nonneg _) (by positivity)
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

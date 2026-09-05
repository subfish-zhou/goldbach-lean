import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrenceStrictCeil
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceSigmaFinal

open scoped Classical BigOperators
open Finset Filter Topology

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Lemma 14.4: `Σ₀` at the single source endpoint

The low-prime part is first recombined at its one endpoint, exactly in source
order.  The strict natural-ceiling carrier makes the odd-depth source condition
automatic once the exponent is at least three.  Claim 14.5 is then applied once
to the resulting `T_N`; no prime-dependent threshold or uniformity premise is
used.
-/

/-- At a single real endpoint `D^(1/σ)`, the strict low-prime carrier is exactly
the support below its natural ceiling.  For `σ ≥ 3`, the natural-ceiling
recurrence therefore recombines `Σ₀` into one value of `suzukiActualT`, without
a separate odd-depth cube hypothesis. -/
theorem suzukiSigmaZero_eq_actualT_single_endpoint_strict
    (S : BoundingSieve) {N D z : ℕ} {σ : ℝ}
    (hN : 2 ≤ N) (hD : 0 < D) (hσ : 3 ≤ σ)
    (hz : (D : ℝ) ^ (1 / σ) ≤ (z : ℝ)) :
    suzukiSigmaZero S N D z ((D : ℝ) ^ (1 / σ)) =
      suzukiActualT S N D ⌈(D : ℝ) ^ (1 / σ)⌉₊ := by
  classical
  let a : ℝ := (D : ℝ) ^ (1 / σ)
  let za : ℕ := ⌈a⌉₊
  have hcarrier :
      (suzukiSupportedBelow S z).filter (fun p : ℕ => (p : ℝ) < a) =
        suzukiSupportedBelow S za := by
    ext p
    simp only [suzukiSupportedBelow, Finset.mem_filter, za, Nat.lt_ceil]
    constructor
    · rintro ⟨⟨hpP, _⟩, hpa⟩
      exact ⟨hpP, hpa⟩
    · rintro ⟨hpP, hpa⟩
      have hpzR : (p : ℝ) < (z : ℝ) := hpa.trans_le (by simpa [a] using hz)
      have hpz : p < z := by exact_mod_cast hpzR
      exact ⟨⟨hpP, hpz⟩, hpa⟩
  have hrec := suzukiActualT_caseI_recurrence_natCeil
    (S := S) (N := N) (D := D) (z := za) (s := σ) hN hD hσ (by
      simp [za, a])
  unfold suzukiSigmaZero
  change (∑ p ∈ (suzukiSupportedBelow S z).filter
      (fun p : ℕ => (p : ℝ) < a),
      S.nu p * suzukiActualT S (N - 1) (D ⌈/⌉ p) p) = _
  rw [hcarrier]
  exact hrec.symm

/-- Eventual `Σ₀` bound in source order.  Eventual growth of `sourceSigma`
supplies the strict natural-ceiling carrier; the endpoint estimate then invokes
Claim 14.5 once. -/
theorem suzukiSigmaZero_sourceSigma_eventually_strict
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ K C145 : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 < K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hH : Section13HatSourceContract H) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ (D N z : ℕ), D₀ ≤ (D : ℝ) →
      2 ≤ N →
      (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) →
      suzukiSigmaZero S N D z
          ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) ≤
        C145 * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) := by
  rcases claim145_sourceSigma_endpoint_internal S H hΔ0 hΔ1 hd hK hC145
      hlocal hH with ⟨D₀, hD₀, hendpoint⟩
  have hsigma : ∀ᶠ D : ℝ in atTop, 3 ≤ sourceSigma D d := by
    have hloglog : Tendsto (fun D : ℝ => Real.log (Real.log D)) atTop atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    filter_upwards [eventually_ge_atTop (2 : ℝ),
        Real.tendsto_log_atTop.eventually_ge_atTop 1,
        hloglog.eventually_ge_atTop 3] with D hD hlogD hq
    have hDpos : 0 < D := by linarith
    have hlogDpos : 0 < Real.log D := by linarith
    have hlog27D : Real.log (27 * D) = Real.log 27 + Real.log D := by
      rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
    have hinner : Real.log D ≤ Real.log (27 * D) := by
      rw [hlog27D]
      exact le_add_of_nonneg_left (Real.log_nonneg (by norm_num))
    have hell : Real.log (Real.log D) ≤ Real.log (Real.log (27 * D)) :=
      Real.log_le_log hlogDpos hinner
    have hfactor : 1 ≤ (Real.log D) ^ (1 / d) := by
      have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
      have hd7 : 7 < d := by
        have hfrac : 7 ≤ 7 / (1 - Δ) := by
          rw [le_div_iff₀ hβ]
          nlinarith
        exact hfrac.trans_lt hd
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hlogD (by positivity)
    have hell0 : 0 ≤ Real.log (Real.log (27 * D)) := by
      linarith [hq.trans hell]
    rw [sourceSigma]
    calc
      3 ≤ Real.log (Real.log D) := hq
      _ ≤ Real.log (Real.log (27 * D)) := hell
      _ ≤ (Real.log D) ^ (1 / d) * Real.log (Real.log (27 * D)) := by
        nlinarith
  rcases eventually_atTop.1 hsigma with ⟨D₁, hD₁⟩
  refine ⟨max D₀ D₁, hD₀.trans_le (le_max_left _ _), ?_⟩
  intro D N z hD hN hz
  have hD₀' : D₀ ≤ (D : ℝ) := (le_max_left _ _).trans hD
  have hD₁' : D₁ ≤ (D : ℝ) := (le_max_right _ _).trans hD
  have hDpos : 0 < D := by
    have hDgt : (1 : ℝ) < (D : ℝ) := hD₀.trans_le hD₀'
    have hDnat : 1 < D := by exact_mod_cast hDgt
    omega
  rw [suzukiSigmaZero_eq_actualT_single_endpoint_strict S hN hDpos
    (hD₁ (D : ℝ) hD₁') hz]
  exact hendpoint D N hD₀'


end MathlibNt.SieveTheory

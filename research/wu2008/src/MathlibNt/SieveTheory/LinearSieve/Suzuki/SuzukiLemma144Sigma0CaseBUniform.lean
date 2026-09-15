import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrenceStrictCeil
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseBUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaGeometryEventually

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1600000

/-- The strict source carrier at the single `sourceSigma` endpoint recombines
`Σ₀` into the actual parity sum.  The natural ceiling is retained literally;
only primes strictly below it are used in the odd cubic side condition. -/
theorem suzukiSigmaZero_eq_actualT_sourceSigma_strict
    (S : BoundingSieve) {N D z : ℕ} {d : ℝ}
    (hN : 2 ≤ N)
    (hz : (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ))
    (hOddCarrier : Odd N → ∀ p < ⌈(D : ℝ) ^
      (1 / sourceSigma (D : ℝ) d)⌉₊, p ^ 3 < D) :
    suzukiSigmaZero S N D z
        ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) =
      suzukiActualT S N D
        ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊ := by
  classical
  let a : ℝ := (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)
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
  have hrec := suzukiActualT_caseI_recurrence_strict
    (S := S) (N := N) (D := D) (z := za) hN (by
      intro hodd p hp
      exact hOddCarrier hodd p (by simpa [za, a] using hp))
  unfold suzukiSigmaZero
  change (∑ p ∈ (suzukiSupportedBelow S z).filter
      (fun p : ℕ => (p : ℝ) < a),
      S.nu p * suzukiActualT S (N - 1) (D ⌈/⌉ p) p) = _
  rw [hcarrier]
  exact hrec.symm

/-- At even depth the odd side condition is vacuous, so the same exact source
recurrence holds without a cubic-ceiling surrogate. -/
theorem suzukiSigmaZero_eq_actualT_sourceSigma_even
    (S : BoundingSieve) {N D z : ℕ} {d : ℝ}
    (hN : 2 ≤ N) (hEven : Even N)
    (hz : (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ)) :
    suzukiSigmaZero S N D z
        ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) =
      suzukiActualT S N D
        ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊ := by
  apply suzukiSigmaZero_eq_actualT_sourceSigma_strict S hN hz
  intro hOdd
  exact (Nat.not_even_iff_odd.mpr hOdd hEven).elim

/-- Source-large, non-eventual `Σ₀` closure, with all Case-B constants selected
uniformly before the varying bounding sieve `S`, then before `C1`, the common
constant `C`, `K`, depth and `D`.  The displayed relative coefficient is exactly
`CB / C`; allowing `C ≥ CB` makes it at most one. -/
theorem claim145_caseB_sigmaZero_uniform_strict_in_S
    (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hTheta : 1 ≤ Θ)
    (hH : Section13HatSourceContract H) :
    ∃ C1min CB : ℝ, 0 < C1min ∧ 0 < CB ∧
      ∀ S : BoundingSieve, ∀ (C1 C K : ℝ) (N D z : ℕ),
        C1min ≤ C1 → CB ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K → 2 ≤ D →
        C1 * K ^ Θ < Real.log (D : ℝ) → 2 ≤ N →
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) →
        suzukiSigmaZero S N D z
            ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) ≤
          (CB / C) * (C * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) := by
  obtain ⟨C1B, CB, hC1B, hCB, hcaseB⟩ :=
    claim145_caseB_uniform_in_S H hΔ0 hΔ1 hd hTheta hH
  obtain ⟨D3, hD3, hsigma3⟩ :=
    exists_sourceSigma_three_threshold d (by
      have hden : 0 < 1 - Δ := sub_pos.mpr hΔ1
      have hfrac : 0 < 7 / (1 - Δ) := div_pos (by norm_num) hden
      linarith)
  let C1min : ℝ := max C1B (Real.log D3)
  have hC1min : 0 < C1min := hC1B.trans_le (le_max_left _ _)
  refine ⟨C1min, CB, hC1min, hCB, ?_⟩
  intro S C1 C K N D z hC1 hCBC hK hlocal hD hlarge hN hz
  have hC1B' : C1B ≤ C1 := (le_max_left _ _).trans hC1
  have hlogD3 : Real.log D3 ≤ Real.log (D : ℝ) := by
    calc
      Real.log D3 ≤ C1min := le_max_right _ _
      _ ≤ C1 := hC1
      _ ≤ C1 * K ^ Θ := by
        have hC10 : 0 ≤ C1 := hC1min.le.trans hC1
        have hKpow : 1 ≤ K ^ Θ :=
          Real.one_le_rpow (by linarith) (by linarith)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hKpow hC10
      _ ≤ Real.log (D : ℝ) := hlarge.le
  have hD3D : D3 ≤ (D : ℝ) := by
    have hexp := Real.exp_le_exp.mpr hlogD3
    rw [Real.exp_log (by linarith : 0 < D3),
      Real.exp_log (by positivity : 0 < (D : ℝ))] at hexp
    exact hexp
  have hσ3 : 3 ≤ sourceSigma (D : ℝ) d := hsigma3 _ hD3D
  have hendpoint : ActualClaim145BoundAt S H N D d Δ K
      (sourceSigma (D : ℝ) d) CB :=
    hcaseB S C1 K N D (sourceSigma (D : ℝ) d)
      hC1B' hK hlocal hD (by linarith [hσ3]) hlarge le_rfl
  have hDpos : 0 < D := by omega
  have hEq := suzukiSigmaZero_eq_actualT_sourceSigma_strict
    (S := S) (N := N) (D := D) (z := z) (d := d) hN hz (by
      intro _ p hp
      exact cube_lt_of_lt_natCeil_rpow hDpos hσ3 rfl hp)
  rw [hEq]
  unfold ActualClaim145BoundAt at hendpoint
  have hCpos : 0 < C := hCB.trans_le hCBC
  calc
    suzukiActualT S N D ⌈(D : ℝ) ^
          (1 / sourceSigma (D : ℝ) d)⌉₊ ≤
        CB * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) := hendpoint
    _ = (CB / C) * (C * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) := by
      field_simp [ne_of_gt hCpos]

/-- Compatibility specialization of the strict uniform-in-`S` Case-B closure. -/
theorem claim145_caseB_sigmaZero_uniform_strict
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hTheta : 1 ≤ Θ)
    (hH : Section13HatSourceContract H) :
    ∃ C1min CB : ℝ, 0 < C1min ∧ 0 < CB ∧
      ∀ (C1 C K : ℝ) (N D z : ℕ),
        C1min ≤ C1 → CB ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K → 2 ≤ D →
        C1 * K ^ Θ < Real.log (D : ℝ) → 2 ≤ N →
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) →
        suzukiSigmaZero S N D z
            ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) ≤
          (CB / C) * (C * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) := by
  obtain ⟨C1min, CB, hC1min, hCB, hall⟩ :=
    claim145_caseB_sigmaZero_uniform_strict_in_S H hΔ0 hΔ1 hd hTheta hH
  exact ⟨C1min, CB, hC1min, hCB, hall S⟩

/-- Even-depth specialization, still uniform in the varying bounding sieve. -/
theorem claim145_caseB_sigmaZero_uniform_even_in_S
    (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hTheta : 1 ≤ Θ)
    (hH : Section13HatSourceContract H) :
    ∃ C1min CB : ℝ, 0 < C1min ∧ 0 < CB ∧
      ∀ S : BoundingSieve, ∀ (C1 C K : ℝ) (N D z : ℕ),
        C1min ≤ C1 → CB ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K → 2 ≤ D →
        C1 * K ^ Θ < Real.log (D : ℝ) → Even N → 2 ≤ N →
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) →
        suzukiSigmaZero S N D z
            ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) ≤
          (CB / C) * (C * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) := by
  obtain ⟨C1min, CB, hC1min, hCB, hstrict⟩ :=
    claim145_caseB_sigmaZero_uniform_strict_in_S H hΔ0 hΔ1 hd hTheta hH
  refine ⟨C1min, CB, hC1min, hCB, ?_⟩
  intro S C1 C K N D z hC1 hCBC hK hlocal hD hlarge _hEven hN hz
  exact hstrict S C1 C K N D z hC1 hCBC hK hlocal hD hlarge hN hz

/-- Compatibility specialization of the even uniform-in-`S` Case-B closure. -/
theorem claim145_caseB_sigmaZero_uniform_even
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hTheta : 1 ≤ Θ)
    (hH : Section13HatSourceContract H) :
    ∃ C1min CB : ℝ, 0 < C1min ∧ 0 < CB ∧
      ∀ (C1 C K : ℝ) (N D z : ℕ),
        C1min ≤ C1 → CB ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K → 2 ≤ D →
        C1 * K ^ Θ < Real.log (D : ℝ) → Even N → 2 ≤ N →
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) →
        suzukiSigmaZero S N D z
            ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) ≤
          (CB / C) * (C * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) := by
  obtain ⟨C1min, CB, hC1min, hCB, hall⟩ :=
    claim145_caseB_sigmaZero_uniform_even_in_S H hΔ0 hΔ1 hd hTheta hH
  exact ⟨C1min, CB, hC1min, hCB, hall S⟩


end MathlibNt.SieveTheory

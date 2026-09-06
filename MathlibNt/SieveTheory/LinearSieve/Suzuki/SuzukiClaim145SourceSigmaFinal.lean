import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseBAllS
-- Keep the legacy endpoint scalar API available to existing imports.
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145ScalarEventual
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiLowerFinal

open scoped Classical BigOperators
open Filter Topology

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- Literal all-`s` Case-B interface.  The source scalar inequalities are kept
 elementary: they mention neither the discrete tail nor `claim14_5Scale`.  This
 separates the actual Lemma-14.3/(14.6) closure from the remaining uniform
 calculus estimate. -/
theorem claim145_sourceSigma_allS_internal_of_scalar
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ K C145 D₀ C M : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 < K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hM3 : 3 ≤ M)
    (hprop : ∀ (sign : ErrorSign) (t : ℝ), M ≤ t →
      proposition131iiLowerProfile C t ≤ H.T sign t)
    (hD₀ : 1 < D₀)
    (hscalar : ∀ (D : ℕ) (s : ℝ), D₀ ≤ (D : ℝ) →
      sourceSigma (D : ℝ) d ≤ s →
      0 < sourceSigma (D : ℝ) d ∧ M ≤ s ∧
      Real.exp 1 * suzukiSourceL (D : ℝ) K ≤ s - 2 ∧
      Real.exp
          (suzukiSourceL (D : ℝ) K +
            (s - 2) *
              (1 + Real.log (suzukiSourceL (D : ℝ) K) - Real.log (s - 2))) ≤
        C145 *
          (claim14_5VProduct S (D : ℝ) *
            (Real.exp (Real.sqrt K) /
              (Real.log (D : ℝ) * sourceSigma (D : ℝ) d)) *
            ((1 + s ^ d / Real.log (D : ℝ)) ^ s * s *
              proposition131iiLowerProfile C s) *
            (Real.log (D : ℝ)) ^ (-Δ))) :
    ∀ (D N : ℕ) (s : ℝ), D₀ ≤ (D : ℝ) →
      sourceSigma (D : ℝ) d ≤ s →
      suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
        C145 * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K s := by
  intro D N s hD hsσ
  have hDreal : 1 < (D : ℝ) := hD₀.trans_le hD
  have hDnat : 2 ≤ D := by exact_mod_cast hDreal
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  have hd7 : 7 < d := by
    have hfrac : 7 ≤ 7 / (1 - Δ) := by
      rw [le_div_iff₀ hβ]
      nlinarith
    exact hfrac.trans_lt hd
  have hd0 : 0 < d := by linarith
  have hdata := hscalar D s hD hsσ
  exact suzukiLemma14_3_le_claim145Scale_of_scalar_at S H hlocal hDnat
    hdata.1 (by linarith [hdata.2.1, hM3]) hdata.2.1 hK hC145.le hprop
    hdata.2.2.1 hdata.2.2.2

/-- Source-faithful Claim 14.5, Case B, on the complete half-line
`s ≥ sourceSigma D d`.  The common threshold is chosen before `D`, `N`, and
`s`; no support-vanishing or endpoint specialization is used. -/
theorem claim145_sourceSigma_allS_internal
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ K C145 : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 < K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hH : Section13HatSourceContract H) :
    ∃ D₀ : ℝ, 1 < D₀ ∧
      ∀ (D N : ℕ) (s : ℝ), D₀ ≤ (D : ℝ) →
        sourceSigma (D : ℝ) d ≤ s →
        suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
          C145 * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K s := by
  rcases proposition131iiUniformQuantitativeLower_of_source hH with
    ⟨C, M, _hC, hM3, hprop⟩
  have hscalar := claim145_sourceSigma_allS_scalar_eventually
    (C := C) (M := M) S hΔ0 hΔ1 hd hK hC145 hlocal
  have hall : ∀ᶠ D : ℝ in atTop,
      1 < D ∧ ∀ s : ℝ, sourceSigma D d ≤ s →
        0 < sourceSigma D d ∧ M ≤ s ∧
        Real.exp 1 * suzukiSourceL D K ≤ s - 2 ∧
        Real.exp
            (suzukiSourceL D K +
              (s - 2) *
                (1 + Real.log (suzukiSourceL D K) - Real.log (s - 2))) ≤
          C145 *
            (claim14_5VProduct S D *
              (Real.exp (Real.sqrt K) /
                (Real.log D * sourceSigma D d)) *
              ((1 + s ^ d / Real.log D) ^ s * s *
                proposition131iiLowerProfile C s) *
              (Real.log D) ^ (-Δ)) :=
    (eventually_gt_atTop (1 : ℝ)).and hscalar
  rcases eventually_atTop.1 hall with ⟨D₀, hD₀⟩
  have hD₀gt : 1 < D₀ := (hD₀ D₀ le_rfl).1
  refine ⟨D₀, hD₀gt, ?_⟩
  exact claim145_sourceSigma_allS_internal_of_scalar S H hΔ0 hΔ1 hd hK hC145
    hlocal hM3 hprop hD₀gt (fun D s hD hs => (hD₀ (D : ℝ) hD).2 s hs)

/-- Source-faithful Claim 14.5 at Suzuki's moving `sourceSigma` endpoint.
One threshold is chosen before both natural parameters `D` and `N`, and the
endpoint is the literal natural ceiling. -/
theorem claim145_sourceSigma_endpoint_internal
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ K C145 : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 < K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hH : Section13HatSourceContract H) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ (D N : ℕ), D₀ ≤ (D : ℝ) →
      suzukiActualT S N D
          ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊ ≤
        C145 * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) := by
  obtain ⟨D₀, hD₀, hall⟩ :=
    claim145_sourceSigma_allS_internal S H hΔ0 hΔ1 hd hK hC145 hlocal hH
  refine ⟨D₀, hD₀, ?_⟩
  intro D N hD
  exact hall D N (sourceSigma (D : ℝ) d) hD le_rfl

/-- Quantifier-closed full Case-B form, with the positive Claim-14.5 constant
chosen before the common threshold and all three varying parameters. -/
theorem exists_claim145_sourceSigma_allS_internal
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ K : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 < K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hH : Section13HatSourceContract H) :
    ∃ C145 : ℝ, 0 < C145 ∧ ∃ D₀ : ℝ, 1 < D₀ ∧
      ∀ (D N : ℕ) (s : ℝ), D₀ ≤ (D : ℝ) →
        sourceSigma (D : ℝ) d ≤ s →
        suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
          C145 * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K s := by
  refine ⟨1, zero_lt_one, ?_⟩
  exact claim145_sourceSigma_allS_internal S H hΔ0 hΔ1 hd hK zero_lt_one hlocal hH

/-- Quantifier-closed endpoint form: choose the positive Claim-14.5
constant before the common threshold and before both natural parameters. -/
theorem exists_claim145_sourceSigma_endpoint_internal
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ K : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 < K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hH : Section13HatSourceContract H) :
    ∃ C145 : ℝ, 0 < C145 ∧ ∃ D₀ : ℝ, 1 < D₀ ∧
      ∀ (D N : ℕ), D₀ ≤ (D : ℝ) →
        suzukiActualT S N D
            ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊ ≤
          C145 * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) := by
  refine ⟨1, zero_lt_one, ?_⟩
  exact claim145_sourceSigma_endpoint_internal S H hΔ0 hΔ1 hd hK zero_lt_one hlocal hH


end MathlibNt.SieveTheory

import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaDifferentialTail

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The pp. 90--91 input from Proposition 13.1(i),(iii), stated before the
perturbation calculus.  It is only a delayed/current DDE ratio and does not
contain the differential certificate's conclusion. -/
def Proposition131MovingDelayedCurrentRatio
    (H : Section13HatLayers) (sign : ErrorSign) (d M : ℝ) : Prop :=
  0 < d ∧ 1 < M ∧
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    M ≤ sourceSigma D d ∧
    ∀ t : ℝ, M ≤ t →
      2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) *
          weightedHat H sign t ≤
        t * H.T sign.opposite (t - 1)

private lemma slope_le_log
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 ≤ d) (ht : 0 < t) :
    perturbationSlope D d 0 t ≤
      (d + 1) * Real.log (1 + t ^ d / Real.log D) := by
  let z : ℝ := t ^ d / Real.log D
  have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg ht.le _) hlog.le
  have hb : 0 < 1 + z := by linarith
  have hzlog : z / (1 + z) ≤ Real.log (1 + z) := by
    have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
    rw [Real.log_inv] at hi
    have heq : z / (1 + z) = 1 - (1 + z)⁻¹ := by
      field_simp [hb.ne']
      ring
    rw [heq]
    linarith
  have htpow : t * t ^ (d - 1) = t ^ d := by
    calc
      t * t ^ (d - 1) = t ^ (1 : ℝ) * t ^ (d - 1) := by rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + (d - 1)) := (Real.rpow_add ht _ _).symm
      _ = t ^ d := by ring_nf
  have hterm : t * (d * t ^ (d - 1) / Real.log D) /
        (1 + t ^ d / Real.log D) = d * (z / (1 + z)) := by
    dsimp [z]
    rw [show t * (d * t ^ (d - 1) / Real.log D) =
      d * (t * t ^ (d - 1)) / Real.log D by ring, htpow]
    ring
  rw [perturbationSlope]
  simp only [add_zero]
  rw [hterm]
  calc
    Real.log (1 + z) + d * (z / (1 + z)) ≤
        Real.log (1 + z) + d * Real.log (1 + z) := by gcongr
    _ = (d + 1) * Real.log (1 + z) := by ring

private lemma below_cutoff_z_le_one
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d) (ht : 0 < t)
    (hcut : t ≤ (Real.log D) ^ (1 / d)) :
    t ^ d / Real.log D ≤ 1 := by
  have hp := Real.rpow_le_rpow ht.le hcut hd.le
  have hc : ((Real.log D) ^ (1 / d)) ^ d = Real.log D := by
    rw [← Real.rpow_mul hlog.le]
    have : (1 / d) * d = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [hc] at hp
  exact (div_le_one hlog).2 hp

private lemma above_cutoff_one_lt_z
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d)
    (hcut : (Real.log D) ^ (1 / d) < t) :
    1 < t ^ d / Real.log D := by
  have hp := Real.rpow_lt_rpow (Real.rpow_nonneg hlog.le _) hcut hd
  have hc : ((Real.log D) ^ (1 / d)) ^ d = Real.log D := by
    rw [← Real.rpow_mul hlog.le]
    have : (1 / d) * d = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [hc] at hp
  exact (one_lt_div hlog).2 hp

/-- The source delayed/current ratio proves the moving differential certificate
by splitting at `(log D)^(1/d)` exactly as on pp. 90--91. -/
theorem movingDDEAsymptoticCertificate_of_proposition131_ratio
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {d M : ℝ}
    (hratio : Proposition131MovingDelayedCurrentRatio H sign d M) :
    MovingDDEAsymptoticCertificate H sign d M := by
  rcases hratio with ⟨hd, hM, D₀, hD₀, hratio⟩
  let Dm : ℝ := Real.exp (M ^ d)
  have hDm : 1 < Dm := by
    dsimp [Dm]
    exact Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos (by linarith) _)
  let D₁ : ℝ := max D₀ Dm
  refine ⟨D₁, hD₀.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hD₀D : D₀ ≤ D := (le_max_left D₀ Dm).trans hD
  have hDmD : Dm ≤ D := (le_max_right D₀ Dm).trans hD
  have hD1 : 1 < D := hD₀.trans_le hD₀D
  have hlog : 0 < Real.log D := Real.log_pos hD1
  have hMdlog : M ^ d ≤ Real.log D := by
    have hm := Real.strictMonoOn_log.monotoneOn (Real.exp_pos (M ^ d))
      (zero_lt_one.trans hD1) hDmD
    simpa [Dm] using hm
  have hMcut : M ≤ (Real.log D) ^ (1 / d) := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith : 0 ≤ M) d)
      hMdlog (by positivity : 0 ≤ 1 / d)
    have hc : (M ^ d) ^ (1 / d) = M := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ M)]
      have : d * (1 / d) = 1 := by field_simp
      rw [this, Real.rpow_one]
    rwa [hc] at hp
  rcases hratio D hD₀D with ⟨hMσ, hratioD⟩
  refine ⟨hMσ, ?_, ?_⟩
  · intro t hMt hcut
    have ht : 0 < t := by linarith
    let z : ℝ := t ^ d / Real.log D
    let W : ℝ := weightedHat H sign t
    let A : ℝ := t * H.T sign.opposite (t - 1)
    have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg ht.le _) hlog.le
    have hz1 : z ≤ 1 := below_cutoff_z_le_one hlog hd ht hcut
    have hb : 0 < 1 + z := by linarith
    have hW0 : 0 ≤ W := by
      dsimp [W, weightedHat]
      exact mul_nonneg (sq_nonneg t) (hH.positive sign t ht).le
    have hratioRaw := hratioD t hMt
    have hratioOne : 2 * ((d + 1) * W) ≤ A := by
      dsimp [z, W, A] at hratioRaw ⊢
      calc
        2 * ((d + 1) * weightedHat H sign t) =
            2 * (d + 1) * 1 * weightedHat H sign t := by ring
        _ ≤ 2 * (d + 1) * max 1
            (Real.log (1 + t ^ d / Real.log D)) * weightedHat H sign t := by
              gcongr
              exact le_max_left _ _
        _ ≤ t * H.T sign.opposite (t - 1) := hratioRaw
    have hden : (d + 1) * W * (1 + z) ≤ A := by
      have hx0 : 0 ≤ (d + 1) * W := mul_nonneg (by linarith) hW0
      nlinarith
    have hs := slope_le_log hlog hd.le ht
    have hlogz : Real.log (1 + z) ≤ z := by
      linarith [Real.log_le_sub_one_of_pos hb]
    have hsW : W * perturbationSlope D d 0 t ≤ (d + 1) * W * z := by
      calc
        W * perturbationSlope D d 0 t ≤
            W * ((d + 1) * Real.log (1 + z)) := by
              apply mul_le_mul_of_nonneg_left _ hW0
              simpa [z] using hs
        _ ≤ W * ((d + 1) * z) := by gcongr
        _ = (d + 1) * W * z := by ring
    calc
      weightedHat H sign t * perturbationSlope D d 0 t ≤
          (d + 1) * weightedHat H sign t * (t ^ d / Real.log D) := hsW
      _ ≤ t * H.T sign.opposite (t - 1) *
          ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := by
            change (d + 1) * W * z ≤ A * (z / (1 + z))
            rw [show A * (z / (1 + z)) = (A * z) / (1 + z) by ring]
            apply (le_div_iff₀ hb).2
            have hm := mul_le_mul_of_nonneg_right hden hz0
            nlinarith
  · intro t hcut htσ
    have ht : 0 < t := (Real.rpow_pos_of_pos hlog _).trans hcut
    have hMt : M ≤ t := hMcut.trans hcut.le
    let z : ℝ := t ^ d / Real.log D
    let W : ℝ := weightedHat H sign t
    let A : ℝ := t * H.T sign.opposite (t - 1)
    have hz1 : 1 < z := by dsimp [z]; exact above_cutoff_one_lt_z hlog hd hcut
    have hb : 0 < 1 + z := by linarith
    have hW0 : 0 ≤ W := by
      dsimp [W, weightedHat]
      exact mul_nonneg (sq_nonneg t) (hH.positive sign t ht).le
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact (mul_pos ht (hH.positive sign.opposite (t - 1) (by linarith))).le
    have hratioRaw := hratioD t hMt
    have hratioLog : 2 * ((d + 1) * Real.log (1 + z) * W) ≤ A := by
      dsimp [z, W, A] at hratioRaw ⊢
      calc
        2 * ((d + 1) * Real.log (1 + t ^ d / Real.log D) * weightedHat H sign t) =
            2 * (d + 1) * Real.log (1 + t ^ d / Real.log D) * weightedHat H sign t := by ring
        _ ≤ 2 * (d + 1) * max 1
            (Real.log (1 + t ^ d / Real.log D)) * weightedHat H sign t := by
              gcongr
              exact le_max_right _ _
        _ ≤ t * H.T sign.opposite (t - 1) := hratioRaw
    have hhalf : (1 / 2 : ℝ) ≤ z / (1 + z) := by
      apply (le_div_iff₀ hb).2
      linarith
    have hs := slope_le_log hlog hd.le ht
    have hsW : W * perturbationSlope D d 0 t ≤
        (d + 1) * Real.log (1 + z) * W := by
      calc
        W * perturbationSlope D d 0 t ≤
            W * ((d + 1) * Real.log (1 + z)) := by
              apply mul_le_mul_of_nonneg_left _ hW0
              simpa [z] using hs
        _ = (d + 1) * Real.log (1 + z) * W := by ring
    dsimp [z, W, A] at hsW hratioLog hhalf ⊢
    calc
      weightedHat H sign t * perturbationSlope D d 0 t ≤
          (d + 1) * Real.log (1 + t ^ d / Real.log D) * weightedHat H sign t := hsW
      _ ≤ (1 / 2) * (t * H.T sign.opposite (t - 1)) := by linarith
      _ ≤ t * H.T sign.opposite (t - 1) *
          ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := by
            nlinarith


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

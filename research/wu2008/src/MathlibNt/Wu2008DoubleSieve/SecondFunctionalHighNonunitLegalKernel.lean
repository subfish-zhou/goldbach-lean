import MathlibNt.Wu2008DoubleSieve.SecondFunctionalContinuousSlab
import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureBuchstab

/-! Full-dimensional legal Buchstab kernel. No regularity across the legal face is asserted. -/
namespace Wu2008DoubleSieve.HighNonunitLegal
open Set MeasureTheory LiLiuPrereqBuchstab
open scoped BigOperators

variable {n : ℕ}

def legal (j : Fin n) (phi : ℝ) : Set (Fin n → ℝ) :=
  {t | (∑ i, t i) + t j ≤ phi}

noncomputable def G (j : Fin n) (phi : ℝ) (t : Fin n → ℝ) : ℝ :=
  (legal j phi).indicator (fun t => buchstab ((phi - ∑ i, t i) / t j) / t j) t

theorem legal_measurable (j : Fin n) (phi : ℝ) : MeasurableSet (legal j phi) := by
  apply measurableSet_le _ measurable_const
  fun_prop

theorem G_of_legal {j : Fin n} {phi : ℝ} {t : Fin n → ℝ} (ht : t ∈ legal j phi) :
    G j phi t = buchstab ((phi - ∑ i, t i) / t j) / t j :=
  Set.indicator_of_mem ht _

theorem G_of_illegal {j : Fin n} {phi : ℝ} {t : Fin n → ℝ} (ht : t ∉ legal j phi) :
    G j phi t = 0 := Set.indicator_of_notMem ht _

theorem argument_ge_one {j : Fin n} {phi : ℝ} {t : Fin n → ℝ}
    (ht : t ∈ continuousCube n) (hl : t ∈ legal j phi) :
    1 ≤ (phi - ∑ i, t i) / t j := by
  have hj := (ht j (mem_univ j)).1
  apply (le_div_iff₀ (by linarith : 0 < t j)).2
  dsimp [legal] at hl
  linarith

theorem G_bounds (j : Fin n) (phi : ℝ) {t : Fin n → ℝ}
    (ht : t ∈ continuousCube n) : 0 ≤ G j phi t ∧ G j phi t ≤ 10 := by
  by_cases hl : t ∈ legal j phi
  · rw [G_of_legal hl]
    have hu := argument_ge_one ht hl
    have hj := (ht j (mem_univ j)).1
    constructor
    · exact div_nonneg (buchstab_nonneg hu) (by linarith)
    · apply (div_le_iff₀ (by linarith : 0 < t j)).2
      linarith [buchstab_le_one hu]
  · rw [G_of_illegal hl]
    norm_num

theorem G_measurable (j : Fin n) (phi : ℝ) : Measurable (G j phi) := by
  apply Measurable.indicator _ (legal_measurable j phi)
  exact (continuous_buchstab.measurable.comp (by fun_prop)).div (measurable_pi_apply j)

theorem G_weighted_integrable (j : Fin n) (phi : ℝ) :
    IntegrableOn (fun t => G j phi t * continuousDensity t) (continuousCube n) := by
  apply continuousDensity_mul_integrable (G_measurable j phi) (K := 10)
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (G_bounds j phi ht).1]
  exact (G_bounds j phi ht).2

/-- The legal face singles out any chosen coordinate, not necessarily the last. -/
def coefficients (j i : Fin n) : ℝ := 1 + if i = j then 1 else 0

theorem coefficients_sum (j : Fin n) (t : Fin n → ℝ) :
    (∑ i, coefficients j i * t i) = (∑ i, t i) + t j := by
  classical
  simp only [coefficients, add_mul, one_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
  simp

theorem coefficients_nonneg (j i : Fin n) : 0 ≤ coefficients j i := by
  unfold coefficients
  split_ifs <;> norm_num

theorem coefficients_l1 (j : Fin n) : (∑ i, |coefficients j i|) = (n : ℝ) + 1 := by
  simp_rw [abs_of_nonneg (coefficients_nonneg j _)]
  simp [coefficients, Finset.sum_add_distrib]

theorem coefficients_selected (j : Fin n) : 1 ≤ |coefficients j j| := by
  norm_num [coefficients]

theorem legal_slab_bounds (j : Fin n) (phi rho : ℝ) (hrho : 0 ≤ rho) :
    0 ≤ (∫ t in continuousCube n ∩ continuousBand (coefficients j) phi rho,
      continuousDensity t) ∧
    (∫ t in continuousCube n ∩ continuousBand (coefficients j) phi rho,
      continuousDensity t) ≤ (4 : ℝ) ^ (n - 1) * (20 * rho) :=
  continuousSlab_bounds j (coefficients j) phi rho (coefficients_selected j) hrho

private theorem div_small_lower {x b : ℝ} (hx : 0 ≤ x) (hb : 1 / 10 ≤ b) :
    x / b ≤ 10 * x := by
  apply (div_le_iff₀ (by linarith)).2
  nlinarith

/-- A reusable quotient bound on the positive reciprocal cube. -/
theorem quotient_difference {x y b d T : ℝ}
    (hb : 1 / 10 ≤ b) (hd : 1 / 10 ≤ d) (hy : |y| ≤ T) :
    |x / b - y / d| ≤ 10 * |x - y| + 100 * T * |b - d| := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := by linarith
  have hT : 0 ≤ T := (abs_nonneg y).trans hy
  have he : x / b - y / d = (x - y) / b + y * (d - b) / (b * d) := by
    field_simp
    ring
  rw [he]
  have h₁ := div_small_lower (abs_nonneg (x - y)) hb
  have hprod : 1 / 100 ≤ b * d := by nlinarith
  have h₂ : |y| * |d - b| / (b * d) ≤ 100 * T * |b - d| := by
    rw [abs_sub_comm d b]
    apply (div_le_iff₀ (mul_pos hb0 hd0)).2
    have hyy := mul_le_mul_of_nonneg_right hy (abs_nonneg (b - d))
    have hh := mul_le_mul_of_nonneg_left hprod
      (show 0 ≤ 100 * T * |b - d| by positivity)
    nlinarith
  have hh := abs_add_le ((x - y) / b) (y * (d - b) / (b * d))
  rw [abs_div, abs_of_pos hb0, abs_div, abs_mul, abs_of_pos (mul_pos hb0 hd0)] at hh
  linarith only [h₁, h₂, hh]

theorem numerator_bounds {j : Fin n} {phi Phi : ℝ} {t : Fin n → ℝ}
    (hphi : phi ≤ Phi) (ht : t ∈ continuousCube n) (hl : t ∈ legal j phi) :
    0 ≤ phi - ∑ i, t i ∧ phi - ∑ i, t i ≤ Phi := by
  have hj := (ht j (mem_univ j)).1
  have hs : 0 ≤ ∑ i, t i := Finset.sum_nonneg (fun i _ => by
    have hi := (ht i (mem_univ i)).1
    linarith)
  dsimp [legal] at hl
  constructor <;> linarith

theorem sum_oscillation {t t' : Fin n → ℝ} {h : ℝ}
    (hh : ∀ i, |t i - t' i| ≤ h) :
    |(∑ i, t i) - ∑ i, t' i| ≤ (n : ℝ) * h := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |t i - t' i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, h := Finset.sum_le_sum (fun i _ => hh i)
    _ = _ := by simp

/-- Uniform oscillation inside the legal domain; no crossing of u = 1 is allowed. -/
theorem G_oscillation {j : Fin n} {phi Phi h : ℝ} {t t' : Fin n → ℝ}
    (hPhi : 2 ≤ Phi) (hphi : phi ∈ Icc 2 Phi)
    (ht : t ∈ continuousCube n) (ht' : t' ∈ continuousCube n)
    (hl : t ∈ legal j phi) (hl' : t' ∈ legal j phi)
    (hh : ∀ i, |t i - t' i| ≤ h) :
    |G j phi t - G j phi t'| ≤ (100 * ((n : ℝ) + 1) + 1000 * Phi) * h := by
  have hb := (ht j (mem_univ j)).1
  have hd := (ht' j (mem_univ j)).1
  have hu := argument_ge_one ht hl
  have hv := argument_ge_one ht' hl'
  have hn := numerator_bounds hphi.2 ht' hl'
  have hnabs : |phi - ∑ i, t' i| ≤ Phi := by
    rw [abs_of_nonneg hn.1]
    exact hn.2
  have hdiff : |(phi - ∑ i, t i) - (phi - ∑ i, t' i)| =
      |(∑ i, t i) - ∑ i, t' i| := by
    rw [show (phi - ∑ i, t i) - (phi - ∑ i, t' i) =
      -((∑ i, t i) - ∑ i, t' i) by ring, abs_neg]
  have harg := quotient_difference hb hd hnabs (x := phi - ∑ i, t i)
  rw [hdiff] at harg
  have hcoord := mul_le_mul_of_nonneg_left (hh j) (show 0 ≤ 100 * Phi by linarith)
  have hs := sum_oscillation hh
  have harg' : |(phi - ∑ i, t i) / t j - (phi - ∑ i, t' i) / t' j| ≤
      10 * (n : ℝ) * h + 100 * Phi * h := by linarith
  have hw := (primeOrdered_buchstab_lipschitz hu hv).trans harg'
  have habs : |buchstab ((phi - ∑ i, t' i) / t' j)| ≤ 1 := by
    rw [abs_of_nonneg (buchstab_nonneg hv)]
    exact buchstab_le_one hv
  have hg := quotient_difference hb hd habs (x := buchstab ((phi - ∑ i, t i) / t j))
  rw [G_of_legal hl, G_of_legal hl']
  nlinarith only [hg, hw, hh j]

theorem legal_eq_affine (j : Fin n) (phi : ℝ) :
    legal j phi = {t | (∑ i, coefficients j i * t i) ≤ phi} := by
  ext t
  simp only [legal, mem_ofPred_eq, coefficients_sum]

theorem legal_band_eq (j : Fin n) (phi rho : ℝ) :
    continuousBand (coefficients j) phi rho =
      {t | |(∑ i, t i) + t j - phi| ≤ rho} := by
  ext t
  simp only [continuousBand, mem_ofPred_eq, coefficients_sum]

theorem legal_face_null (j : Fin n) (phi : ℝ) :
    volume (continuousCube n ∩ {t | (∑ i, t i) + t j = phi}) = 0 := by
  simpa only [coefficients_sum] using
    continuousHyperplane_null j (coefficients j) phi (coefficients_selected j)

end Wu2008DoubleSieve.HighNonunitLegal

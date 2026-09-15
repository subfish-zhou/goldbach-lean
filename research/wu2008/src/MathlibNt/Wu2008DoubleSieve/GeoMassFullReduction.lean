import MathlibNt.Wu2008DoubleSieve.GeoMassOrderedPure
import MathlibNt.Wu2008DoubleSieve.GeoMassSelectedFibres
import MathlibNt.Wu2008DoubleSieve.GeoMassOriginalBlocks

/-! Exact one-dimensional logarithmic reduction of all twelve original masses. -/
namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.FullReduction
open Set MeasureTheory

noncomputable def logMoment (r q : ℕ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.log (t/a)^r * Real.log (b/t)^q / t^2

/-- Both independent actual integral producers are supplied internally. -/
theorem selectedOrderedMass_eq_log {n : ℕ} (j : Fin n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    selectedOrderedMass j a b =
      logMoment j.val (n-1-j.val) a b /
        ((j.val.factorial : ℝ) * ((n-1-j.val).factorial : ℝ)) := by
  rw [SelectedFibres.selectedOrderedMass_fibre j ha hab]
  calc
    _ = ∫ t in a..b,
        (Real.log (t/a)^j.val * Real.log (b/t)^(n-1-j.val) / t^2) /
          ((j.val.factorial : ℝ) * ((n-1-j.val).factorial : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      dsimp only
      rw [OrderedPure.pureOrderedMass_eq_log j.val ha ht.1,
        OrderedPure.pureOrderedMass_eq_log (n-1-j.val) (ha.trans_le ht.1) ht.2]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [intervalIntegral.integral_div]; rfl

noncomputable def oneDimensionalMass (p : SecondFunctionalParameters) : ℝ :=
  let a := 1/p.S
  let b := 1/p.kappa1
  let c := 1/p.kappa2
  let e := 1/p.kappa3
  let f := 1/p.s
  (Real.log (f/c) * logMoment 1 0 b c +
    Real.log (c/b) * logMoment 0 1 c e +
    Real.log (f/e) * logMoment 1 0 a b + lowerThreeLog p +
    Real.log (b/a) * logMoment 0 1 c f + lowerFiveLog p) +
  ((Real.log (e/c) / 2 * logMoment 2 1 e f + logMoment 4 1 e f / 24) +
    (logMoment 2 1 c e / 2 + Real.log (f/e) / 2 * logMoment 2 0 c e +
      Real.log (e/c)^2 / 2 * logMoment 0 1 e f +
      Real.log (c/b) * logMoment 1 1 e f))

/-- The old M, unchanged, is exactly the explicit sum of one-dimensional integrals. -/
theorem M_one_dimensional (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : SecondFunctionalJointTail.M p = oneDimensionalMass p := by
  obtain ⟨ha,hab,hbc,hce,hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have ha0 : 0 < 1/p.S := by linarith
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  have he0 := hc0.trans_le hce
  rw [OriginalBlocks.M_blocks_exact p hp hs]
  rw [selectedOrderedMass_eq_log (1 : Fin 2) hb0 hbc,
    selectedOrderedMass_eq_log (0 : Fin 2) hc0 hce,
    selectedOrderedMass_eq_log (1 : Fin 2) ha0 hab,
    selectedOrderedMass_eq_log (0 : Fin 2) hc0 (hce.trans hef),
    selectedOrderedMass_eq_log (2 : Fin 4) he0 hef,
    selectedOrderedMass_eq_log (4 : Fin 6) he0 hef,
    selectedOrderedMass_eq_log (2 : Fin 4) hc0 hce,
    selectedOrderedMass_eq_log (2 : Fin 3) hc0 hce,
    selectedOrderedMass_eq_log (0 : Fin 2) he0 hef,
    selectedOrderedMass_eq_log (1 : Fin 3) he0 hef,
    OrderedPure.pureOrderedMass_eq_log 2 hc0 hce]
  norm_num [oneDimensionalMass]
  ring

theorem logMoment_integrable (r q : ℕ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => Real.log (t/a)^r * Real.log (b/t)^q / t^2) (Icc a b) :=
  log_kernel_integrable r q ha

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.FullReduction

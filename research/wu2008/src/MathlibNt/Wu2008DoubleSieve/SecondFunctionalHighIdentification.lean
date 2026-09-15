import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighSections

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnit
open Set MeasureTheory SecondFunctionalUnitKernel

/-- Measurability of the independently defined full-space section, including closed faces. -/
theorem section20_measurable (a2 a3 b phi : ℝ) : Measurable (section20 a2 a3 b phi) := by
  have hs : MeasurableSet {t : Fin 4 → ℝ | D20 a2 a3 b (append phi t)} := by
    simp only [D20_append, ofPred_and]
    exact (measurableSet_le measurable_const (by fun_prop)).inter
      ((measurableSet_le (by fun_prop) measurable_const).inter
      ((measurableSet_le measurable_const (by fun_prop)).inter
      ((measurableSet_le (by fun_prop) (by fun_prop)).inter
      ((measurableSet_le (by fun_prop) (by fun_prop)).inter
      ((measurableSet_le (by fun_prop) (by fun_prop)).inter
       (measurableSet_le (by fun_prop) measurable_const))))))
  exact Measurable.ite hs (by fun_prop) measurable_const

theorem section21_measurable (a3 b phi : ℝ) : Measurable (section21 a3 b phi) := by
  have hs : MeasurableSet {t : Fin 5 → ℝ | D21 a3 b (append phi t)} := by
    simp only [D21_append, ofPred_and]
    exact (measurableSet_le measurable_const (by fun_prop)).inter
      ((measurableSet_le (by fun_prop) (by fun_prop)).inter
      ((measurableSet_le (by fun_prop) (by fun_prop)).inter
      ((measurableSet_le (by fun_prop) (by fun_prop)).inter
      ((measurableSet_le (by fun_prop) (by fun_prop)).inter
      ((measurableSet_le (by fun_prop) (by fun_prop)).inter
       (measurableSet_le (by fun_prop) measurable_const))))))
  exact Measurable.ite hs (by fun_prop) measurable_const

/-- Full-volume a.e. equality; no pointwise identification of closed and strict faces. -/
theorem section20_ae {a2 a3 b : ℝ} (ha : 1/10 ≤ a2) (hb : b ≤ 1/2) (phi : ℝ) :
    section20 a2 a3 b phi =ᵐ[volume] (continuousCube 4).indicator
      (fun t => G phi b C20 (gamma20 a2 a3 b) flags20 t * continuousDensity t) :=
  closed_section_ae phi b C20 (gamma20 a2 a3 b) flags20 normalized20
    (fun t => D20 a2 a3 b (append phi t)) (D20_closed_dictionary a2 a3 b phi)
    (fun _ ht => D20_cube ha hb ht)

theorem section21_ae {a3 b : ℝ} (ha : 1/10 ≤ a3) (hb : b ≤ 1/2) (phi : ℝ) :
    section21 a3 b phi =ᵐ[volume] (continuousCube 5).indicator
      (fun t => G phi b C21 (gamma21 a3 b) flags21 t * continuousDensity t) :=
  closed_section_ae phi b C21 (gamma21 a3 b) flags21 normalized21
    (fun t => D21 a3 b (append phi t)) (D21_closed_dictionary a3 b phi)
    (fun _ ht => D21_cube ha hb ht)

/-- These producers require no integrability or domain-identity input. Window order is unnecessary. -/
theorem section20_integrable {a2 a3 b : ℝ} (ha : 1/10 ≤ a2) (hb : b ≤ 1/2) (phi : ℝ) :
    Integrable (section20 a2 a3 b phi) :=
  closed_section_integrable phi b C20 (gamma20 a2 a3 b) flags20 normalized20
    (fun t => D20 a2 a3 b (append phi t)) (D20_closed_dictionary a2 a3 b phi)
    (fun _ ht => D20_cube ha hb ht)

theorem section21_integrable {a3 b : ℝ} (ha : 1/10 ≤ a3) (hb : b ≤ 1/2) (phi : ℝ) :
    Integrable (section21 a3 b phi) :=
  closed_section_integrable phi b C21 (gamma21 a3 b) flags21 normalized21
    (fun t => D21 a3 b (append phi t)) (D21_closed_dictionary a3 b phi)
    (fun _ ht => D21_cube ha hb ht)

/-- Actual Lebesgue unit-section integrals, with no extra last-coordinate weight or factorial. -/
theorem J20_identification {a2 a3 b : ℝ} (ha : 1/10 ≤ a2) (hb : b ≤ 1/2) (phi : ℝ) :
    J20 a2 a3 b phi = ∫ t in continuousCube 4,
      G phi b C20 (gamma20 a2 a3 b) flags20 t * continuousDensity t := by
  unfold J20
  rw [integral_congr_ae (section20_ae ha hb phi), integral_indicator (continuousCube_measurable 4)]

theorem J21_identification {a3 b : ℝ} (ha : 1/10 ≤ a3) (hb : b ≤ 1/2) (phi : ℝ) :
    J21 a3 b phi = ∫ t in continuousCube 5,
      G phi b C21 (gamma21 a3 b) flags21 t * continuousDensity t := by
  unfold J21
  rw [integral_congr_ae (section21_ae ha hb phi), integral_indicator (continuousCube_measurable 5)]

/-- Zero-width consumers preserve every real phi, and do not assert the closed D set is empty. -/
theorem J20_zero_left {a b : ℝ} (ha : 1/10 ≤ a) (hb : b ≤ 1/2) (phi : ℝ) :
    J20 a a b phi = 0 := by
  rw [J20_identification ha hb phi]
  simp [G, dictionary20, Q20_empty_left]

theorem J20_zero_right {a b : ℝ} (ha : 1/10 ≤ a) (hb : b ≤ 1/2) (phi : ℝ) :
    J20 a b b phi = 0 := by
  rw [J20_identification ha hb phi]
  simp [G, dictionary20, Q20_empty_right]

theorem J21_zero {a : ℝ} (ha : 1/10 ≤ a) (hb : a ≤ 1/2) (phi : ℝ) :
    J21 a a phi = 0 := by
  rw [J21_identification ha hb phi]
  simp [G, dictionary21, Q21_empty]

/-- Bundled consumer: the integrability and the identity have actual producers. -/
theorem J20_spec {a2 a3 b : ℝ} (ha : 1/10 ≤ a2) (hb : b ≤ 1/2) (phi : ℝ) :
    Measurable (section20 a2 a3 b phi) ∧ Integrable (section20 a2 a3 b phi) ∧
    J20 a2 a3 b phi = ∫ t in continuousCube 4,
      G phi b C20 (gamma20 a2 a3 b) flags20 t * continuousDensity t :=
  ⟨section20_measurable a2 a3 b phi, section20_integrable ha hb phi,
    J20_identification ha hb phi⟩

theorem J21_spec {a3 b : ℝ} (ha : 1/10 ≤ a3) (hb : b ≤ 1/2) (phi : ℝ) :
    Measurable (section21 a3 b phi) ∧ Integrable (section21 a3 b phi) ∧
    J21 a3 b phi = ∫ t in continuousCube 5,
      G phi b C21 (gamma21 a3 b) flags21 t * continuousDensity t :=
  ⟨section21_measurable a3 b phi, section21_integrable ha hb phi,
    J21_identification ha hb phi⟩

end Wu2008DoubleSieve.HighUnit

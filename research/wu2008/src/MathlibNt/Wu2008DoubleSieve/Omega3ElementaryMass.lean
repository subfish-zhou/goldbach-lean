import MathlibNt.Wu2008DoubleSieve.Omega3ElementaryGate

namespace Wu2008DoubleSieve.Omega3ElementaryMass
open Set MeasureTheory SecondFunctionalGeometricMass SecondFunctionalJointTail
open SecondFunctionalGeometricMass.SelectedFibres
open scoped BigOperators

/-- Removing the first coordinate preserves all closed order constraints. -/
theorem domain_cons {n : ℕ} (l h x : ℝ) (t : Fin n → ℝ) :
    Fin.cons x t ∈ orderedDomain (n+1) l h ↔
      x ∈ Icc l h ∧ t ∈ orderedDomain n x h := by
  constructor
  · rintro ⟨hb,hm⟩
    refine ⟨by simpa using hb 0, ?_, ?_⟩
    · intro i
      exact ⟨by simpa using hm (Fin.zero_le i.succ), by simpa using (hb i.succ).2⟩
    · intro i j hij
      simpa using hm (Fin.succ_le_succ_iff.mpr hij)
  · rintro ⟨hx,ht,hm⟩
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using And.intro (hx.1.trans (ht j).1) (ht j).2
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact le_rfl
        | succ j => simpa using (ht j).1
      | succ i =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j => simpa using hm (Fin.succ_le_succ_iff.mp hij)

theorem weight_cons {n : ℕ} (j : Fin n) (x : ℝ) (t : Fin n → ℝ) :
    geometricWeight j.succ (Fin.cons x t) = (1/x) * geometricWeight j t := by
  simp only [geometricWeight, continuousDensity, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  ring

/-- Actual first-coordinate Fubini, with the accepted absolute-integrability producer. -/
theorem selected_succ {n : ℕ} (j : Fin n) {l h : ℝ} (hl : 0 < l) (hlh : l ≤ h) :
    selectedOrderedMass j.succ l h =
      ∫ x in l..h, (1/x) * selectedOrderedMass j x h := by
  classical
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have he (p : ℝ × (Fin n → ℝ)) : e p = Fin.cons p.1 p.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hp : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  let f := (orderedDomain (n+1) l h).indicator (geometricWeight j.succ)
  have hi : Integrable f := (selected_integrable j.succ (b := h) hl).integrable_indicator
    (orderedDomain_measurable _ l h)
  have hc := (hp.integrable_comp_emb e.measurableEmbedding).mpr hi
  have hind (x : ℝ) (t : Fin n → ℝ) : f (Fin.cons x t) =
      (Icc l h).indicator (fun x => (1/x) *
        (orderedDomain n x h).indicator (geometricWeight j) t) x := by
    by_cases hx : x ∈ Icc l h
    · by_cases ht : t ∈ orderedDomain n x h
      · simp [f, domain_cons, hx, ht, weight_cons]
      · simp [f, domain_cons, hx, ht]
    · simp [f, domain_cons, hx]
  change (∫ t in orderedDomain (n+1) l h, geometricWeight j.succ t) = _
  rw [← integral_indicator (orderedDomain_measurable _ l h)]
  change (∫ t, f t) = _
  rw [← hp.integral_comp' f]
  change (∫ p, (f ∘ e) p) = _
  rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = volume.prod volume from rfl,
    integral_prod _ hc]
  simp only [Function.comp_apply]
  simp_rw [he, hind]
  calc
    _ = ∫ x : ℝ, (Icc l h).indicator
        (fun x => (1/x) * selectedOrderedMass j x h) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Icc l h
      · simp only [indicator_of_mem hx]
        rw [integral_const_mul, integral_indicator (orderedDomain_measurable n x h)]
        rfl
      · simp [hx]
    _ = _ := by
      rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hlh]

/-- The literal reciprocal inner fibre, with positive endpoints. -/
theorem inner_eq {a b h : ℝ} (hb : 0 < b) (hbh : b ≤ h) :
    (∫ c in b..h, (1 : ℝ)/(a*b^2*c)) = (1/a) * (Real.log (h/b)/b^2) := by
  calc
    _ = (1/(a*b^2)) * (∫ c in b..h, 1/c) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro c _
      dsimp
      ring
    _ = _ := by rw [integral_one_div_of_pos hb (hb.trans_le hbh)]; ring

/-- The original nested ordered mass is exactly the accepted selected-coordinate mass. -/
theorem nested_eq_selected {l h : ℝ} (hl : 0 < l) (hlh : l ≤ h) :
    (∫ a in l..h, ∫ b in a..h, ∫ c in b..h, (1 : ℝ)/(a*b^2*c)) =
      selectedOrderedMass (1 : Fin 3) l h := by
  rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl, selected_succ _ hl hlh]
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hlh] at ha
  have ha0 := hl.trans_le ha.1
  dsimp only
  rw [selectedOrderedMass_fibre (0 : Fin 2) ha0 ha.2]
  simp only [Fin.val_zero, show 2-1=1 from rfl, pure_zero, one_mul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro b hb
  rw [uIcc_of_le ha.2] at hb
  have hb0 := ha0.trans_le hb.1
  dsimp only
  rw [OrderedPure.pureOrderedMass_eq_log 1 hb0 hb.2]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  exact inner_eq hb0 hb.2

/-- Exact elementary expression, not a cube cap or a factorial overestimate. -/
theorem nested_eq_elementary {l h : ℝ} (hl : 0 < l) (hlh : l ≤ h) :
    (∫ a in l..h, ∫ b in a..h, ∫ c in b..h, (1 : ℝ)/(a*b^2*c)) =
      Elementary.elementaryMomentOne 1 l h := by
  rw [nested_eq_selected hl hlh, FullReduction.selectedOrderedMass_eq_log (1 : Fin 3) hl hlh]
  norm_num only [Fin.val_one, Nat.factorial, Nat.reduceSub, Nat.cast_one, mul_one, div_one]
  exact Elementary.logMoment_one_eq 1 hl hlh

end Wu2008DoubleSieve.Omega3ElementaryMass

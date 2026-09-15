import MathlibNt.Wu2008DoubleSieve.GeoMassOrderedBase

namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.OrderedPure
open Set MeasureTheory
open scoped BigOperators

theorem orderedDomain_measurable (n : ℕ) (a b : ℝ) :
    MeasurableSet (orderedDomain n a b) := by
  have he : orderedDomain n a b =
      (⋂ i, {t : Fin n → ℝ | t i ∈ Icc a b}) ∩
      (⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {t : Fin n → ℝ | t i ≤ t j}) := by
    ext t
    simp only [orderedDomain, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rfl
  rw [he]
  exact (MeasurableSet.iInter fun i => measurableSet_Icc.preimage (measurable_pi_apply i)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j))

theorem pure_rectangle_integrable (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (continuousDensity (n := n)) (Set.pi Set.univ (fun _ => Icc a b)) := by
  change Integrable _ ((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict _)
  rw [Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (fun _ =>
    (continuousOn_const.div continuousOn_id
      (fun _ hx => ne_of_gt (ha.trans_le hx.1))).integrableOn_Icc)

theorem pureOrderedMass_integrable (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (continuousDensity (n := n)) (orderedDomain n a b) := by
  apply (pure_rectangle_integrable n (b := b) ha).mono_set
  intro t ht i _
  exact ht.1 i

theorem pureOrderedMass_zero (a b : ℝ) : pureOrderedMass 0 a b = 1 := by
  have he : orderedDomain 0 a b = Set.univ := by
    ext t
    simp only [mem_orderedDomain, mem_univ, iff_true]
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  simp [pureOrderedMass, he, continuousDensity, measureReal_def,
    show (volume : Measure (Fin 0 → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.pi_empty_univ]

theorem mem_orderedDomain_snoc {n : ℕ} (a b x : ℝ) (t : Fin n → ℝ) :
    Fin.snoc t x ∈ orderedDomain (n+1) a b ↔
      x ∈ Icc a b ∧ t ∈ orderedDomain n a x := by
  constructor
  · rintro ⟨hb, hm⟩
    refine ⟨by simpa using hb (Fin.last n), ?_, ?_⟩
    · intro i
      exact ⟨by simpa using (hb i.castSucc).1,
        by simpa using hm (Fin.le_last i.castSucc)⟩
    · intro i j hij
      simpa using hm (Fin.castSucc_le_castSucc_iff.mpr hij)
  · rintro ⟨hx, ht, hm⟩
    constructor
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using And.intro (ht j).1 ((ht j).2.trans hx.2)
    · intro i j hij
      revert hij
      refine Fin.lastCases ?_ (fun jj => ?_) j
      · intro _
        refine Fin.lastCases ?_ (fun ii => ?_) i
        · simp only [Fin.snoc_last, le_refl]
        · simpa using (ht ii).2
      · refine Fin.lastCases ?_ (fun ii => ?_) i
        · intro h
          have : (Fin.last n : Fin (n+1)) ≤ jj.castSucc := h
          have hj := jj.isLt
          simp only [Fin.le_iff_val_le_val, Fin.val_last, Fin.val_castSucc] at this
          omega
        · intro h
          simpa using hm (Fin.castSucc_le_castSucc_iff.mp h)

theorem continuousDensity_snoc {n : ℕ} (t : Fin n → ℝ) (x : ℝ) :
    continuousDensity (Fin.snoc t x) = continuousDensity t * (1/x) := by
  simp [continuousDensity, Fin.prod_univ_castSucc, mul_comm]

theorem integral_last_coordinate {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : Integrable f) :
    (∫ t, f t) = ∫ x : ℝ, ∫ t : Fin n → ℝ, f (Fin.snoc t x) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)).symm
  have he (p : ℝ × (Fin n → ℝ)) : e p = Fin.snoc p.2 p.1 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_last']
  have hp : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)).symm
  have hi : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.snoc p.2 p.1)) := by
    simpa only [Function.comp_def, he] using
      (hp.integrable_comp_emb e.measurableEmbedding).mpr hf
  calc
    _ = ∫ p : ℝ × (Fin n → ℝ), f (Fin.snoc p.2 p.1) := by
      simpa only [he] using (hp.integral_comp' f).symm
    _ = _ := integral_prod _ hi

private theorem indicator_snoc {n : ℕ} (a b x : ℝ) (t : Fin n → ℝ) :
    (orderedDomain (n+1) a b).indicator continuousDensity (Fin.snoc t x) =
      (Icc a b).indicator
        (fun y => (orderedDomain n a y).indicator continuousDensity t * (1/y)) x := by
  classical
  by_cases hx : x ∈ Icc a b
  · by_cases ht : t ∈ orderedDomain n a x
    · simp [hx, ht, mem_orderedDomain_snoc, continuousDensity_snoc]
    · simp [hx, ht, mem_orderedDomain_snoc]
  · simp [hx, mem_orderedDomain_snoc]

/-- Actual last-coordinate Fubini, with absolute integrability supplied internally. -/
theorem pureOrderedMass_succ (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    pureOrderedMass (n+1) a b = ∫ x in Icc a b, pureOrderedMass n a x * (1/x) := by
  rw [pureOrderedMass, ← integral_indicator (orderedDomain_measurable (n+1) a b)]
  rw [integral_last_coordinate _
    ((pureOrderedMass_integrable (n+1) (b := b) ha).integrable_indicator
      (orderedDomain_measurable (n+1) a b))]
  simp_rw [indicator_snoc]
  calc
    _ = ∫ x : ℝ, (Icc a b).indicator (fun y => pureOrderedMass n a y * (1/y)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Icc a b
      · simp only [indicator_of_mem hx]
        rw [integral_mul_const, integral_indicator (orderedDomain_measurable n a x)]
        rfl
      · simp only [indicator_of_notMem hx, integral_zero]
    _ = _ := integral_indicator measurableSet_Icc

/-- The genuine ordered reciprocal-density integral in every dimension. -/
theorem pureOrderedMass_eq_log (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    pureOrderedMass n a b = Real.log (b/a)^n / (n.factorial : ℝ) := by
  induction n generalizing b with
  | zero => simp [pureOrderedMass_zero]
  | succ n ih =>
    rw [pureOrderedMass_succ n ha]
    calc
      _ = ∫ x in Icc a b, Real.log (x/a)^n / ((n.factorial : ℝ) * x) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        dsimp only
        rw [ih hx.1]
        ring
      _ = _ := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
        exact factorial_fibre_step n ha hab

theorem pureOrderedMass_same (n : ℕ) {a : ℝ} (ha : 0 < a) :
    pureOrderedMass (n+1) a a = 0 := by
  rw [pureOrderedMass_eq_log (n+1) ha le_rfl]
  simp [ha.ne']

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.OrderedPure

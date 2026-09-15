import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitLegalMass
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleGroupedActual

/-! Six literal closed lower-triple domains. This does not transport the shifted
finite lower endpoint: null continuous faces can still contain prime atoms. -/
namespace Wu2008DoubleSieve.LowerTripleContinuous
open Set MeasureTheory
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

def CompactParameters (a b c e f : ℝ) : Prop :=
  1 / 10 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ e ∧ e ≤ f ∧ f ≤ 1 / 2

/-- All six endpoints come directly from the accepted independent band dictionary. -/
noncomputable def D (a b c e f : ℝ) (j : Fin 6) : Set Point :=
  let v := LowerTripleGrouped.bands a b c e f j
  {t | v.1 ≤ t 0 ∧ t 0 ≤ v.2.1 ∧ v.2.2.1 ≤ t 1 ∧ t 1 ≤ v.2.2.2.1 ∧
    v.2.2.2.2.1 ≤ t 2 ∧ t 2 ≤ v.2.2.2.2.2 ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2}

noncomputable abbrev G (phi : ℝ) : Point → ℝ := HighNonunitLegal.G 1 phi

 theorem D_closed (a b c e f : ℝ) (j : Fin 6) : IsClosed (D a b c e f j) := by
  unfold D
  simp only [ofPred_and]
  repeat' apply IsClosed.inter
  all_goals apply isClosed_le <;> fun_prop

theorem D_measurable (a b c e f : ℝ) (j : Fin 6) : MeasurableSet (D a b c e f j) :=
  (D_closed a b c e f j).measurableSet

theorem bands_outer_bounds {a b c e f : ℝ} (hp : CompactParameters a b c e f)
    (j : Fin 6) : a ≤ (LowerTripleGrouped.bands a b c e f j).1 ∧
      (LowerTripleGrouped.bands a b c e f j).2.2.2.2.2 ≤ f := by
  rcases hp with ⟨ha, hab, hbc, hce, hef, hf⟩
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))))) j
  all_goals simp only [LowerTripleGrouped.bands, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals constructor <;> linarith

theorem D_subset_cube {a b c e f : ℝ} (hp : CompactParameters a b c e f)
    (j : Fin 6) : D a b c e f j ⊆ continuousCube 3 := by
  intro t ht
  obtain ⟨hlo, hhi⟩ := bands_outer_bounds hp j
  rcases hp with ⟨ha, hab, hbc, hce, hef, hf⟩
  rcases ht with ⟨h0, h1, h2, h3, h4, h5, h01, h12⟩
  simp only [continuousCube, mem_pi, mem_univ, forall_const, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true]
  dsimp
  repeat' constructor
  all_goals linarith

theorem sum_literal (t : Point) : (∑ i, t i) = t 0 + t 1 + t 2 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change t 0 + (t 1 + t 2) = _
  ring

/-- The full cube, including the phi=2 boundary, is legal in this dimension. -/
theorem cube_legal {phi : ℝ} (hphi : 2 ≤ phi) :
    continuousCube 3 ⊆ HighNonunitLegal.legal 1 phi := by
  intro t ht
  have h0 := (ht 0 (mem_univ _)).2
  have h1 := (ht 1 (mem_univ _)).2
  have h2 := (ht 2 (mem_univ _)).2
  change (∑ i, t i) + t 1 ≤ phi
  rw [sum_literal]
  linarith

theorem G_cube_literal {phi : ℝ} (hphi : 2 ≤ phi) {t : Point}
    (ht : t ∈ continuousCube 3) :
    G phi t = LiLiuPrereqBuchstab.buchstab ((phi - (t 0 + t 1 + t 2)) / t 1) / t 1 := by
  change HighNonunitLegal.G (1 : Fin 3) phi t = _
  rw [HighNonunitLegal.G_of_legal (cube_legal hphi ht), sum_literal]

theorem G_measurable (phi : ℝ) : Measurable (G phi) := HighNonunitLegal.G_measurable 1 phi

theorem weighted_measurable (phi : ℝ) :
    Measurable (fun t : Point => G phi t * continuousDensity t) := by
  apply (G_measurable phi).mul
  unfold continuousDensity
  fun_prop

noncomputable def K (a b c e f : ℝ) (j : Fin 6) (phi : ℝ) : ℝ :=
  ∫ t in D a b c e f j, G phi t * continuousDensity t

theorem K_integrable {a b c e f : ℝ} (hp : CompactParameters a b c e f)
    (j : Fin 6) (phi : ℝ) :
    IntegrableOn (fun t => G phi t * continuousDensity t) (D a b c e f j) :=
  HighNonunitLegal.weighted_integrable_on 1 phi (D_subset_cube hp j)

theorem K_bounds {a b c e f : ℝ} (hp : CompactParameters a b c e f)
    (j : Fin 6) (phi : ℝ) :
    0 ≤ K a b c e f j phi ∧ K a b c e f j phi ≤ 10 * (4 : ℝ) ^ 3 :=
  HighNonunitLegal.integral_bounds 1 phi (D_measurable a b c e f j) (D_subset_cube hp j)

/-- Exactly q squared, with no duplicated reciprocal from G. -/
theorem weighted_legal_literal {phi : ℝ} {t : Point}
    (hl : t ∈ HighNonunitLegal.legal 1 phi) :
    G phi t * continuousDensity t =
      LiLiuPrereqBuchstab.buchstab ((phi - (t 0 + t 1 + t 2)) / t 1) /
        (t 0 * t 1 ^ 2 * t 2) := by
  rw [HighNonunitLegal.weighted_formula hl, sum_literal]
  have hd : t 1 * (∏ i, t i) = t 0 * t 1 ^ 2 * t 2 := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change t 1 * (t 0 * (t 1 * t 2)) = _
    ring
  rw [hd]

theorem K_literal {a b c e f phi : ℝ} (hp : CompactParameters a b c e f)
    (hphi : 2 ≤ phi) (j : Fin 6) :
    K a b c e f j phi = ∫ t in D a b c e f j,
      LiLiuPrereqBuchstab.buchstab ((phi - (t 0 + t 1 + t 2)) / t 1) /
        (t 0 * t 1 ^ 2 * t 2) := by
  apply setIntegral_congr_fun (D_measurable a b c e f j)
  intro t ht
  exact weighted_legal_literal (cube_legal hphi (D_subset_cube hp j ht))

theorem literal_integrable {a b c e f phi : ℝ} (hp : CompactParameters a b c e f)
    (hphi : 2 ≤ phi) (j : Fin 6) :
    IntegrableOn (fun t : Point =>
      LiLiuPrereqBuchstab.buchstab ((phi - (t 0 + t 1 + t 2)) / t 1) /
        (t 0 * t 1 ^ 2 * t 2)) (D a b c e f j) :=
  (K_integrable hp j phi).congr_fun
    (fun _ ht => weighted_legal_literal (cube_legal hphi (D_subset_cube hp j ht)))
    (D_measurable a b c e f j)

/-- Actual reciprocal mother coordinates, without changing any parameter. -/
theorem mother_compact_parameters (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    CompactParameters (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) := by
  have hs0 : 0 < p.s := lt_of_lt_of_le zero_lt_one hp.one_le_s
  have he : 0 < p.kappa3 := hs0.trans_le hp.s_le_kappa3
  have hc : 0 < p.kappa2 := he.trans hp.kappa3_lt_kappa2
  have hb : 0 < p.kappa1 := hc.trans hp.kappa2_lt_kappa1
  have ha : 0 < p.S := hb.trans_le hp.kappa1_le_S
  exact ⟨one_div_le_one_div_of_le ha hp.S_le_ten,
    one_div_le_one_div_of_le hb hp.kappa1_le_S,
    one_div_le_one_div_of_le hc hp.kappa2_lt_kappa1.le,
    one_div_le_one_div_of_le he hp.kappa3_lt_kappa2.le,
    one_div_le_one_div_of_le hs0 hp.s_le_kappa3,
    one_div_le_one_div_of_le (by norm_num) hs⟩

/-- No assertion of global continuity across the legal face is used. -/
theorem G_continuousOn_cube {phi : ℝ} (hphi : 2 ≤ phi) :
    ContinuousOn (G phi) (continuousCube 3) := by
  have hd : ∀ t ∈ continuousCube 3, t (1 : Fin 3) ≠ 0 := by
    intro t ht
    have h := (ht 1 (mem_univ _)).1
    linarith
  have hn : Continuous (fun t : Point => phi - (t 0 + t 1 + t 2)) := by fun_prop
  have hc := LiLiuPrereqBuchstab.continuous_buchstab.comp_continuousOn
    (hn.continuousOn.div (continuous_apply 1).continuousOn hd)
  apply (hc.div (continuous_apply 1).continuousOn hd).congr
  intro t ht
  exact G_cube_literal hphi ht

/-- The dictionary has six independent entries, with every displayed endpoint closed. -/
theorem D_six_literal (a b c e f : ℝ) :
    D a b c e f 0 = {t | b ≤ t 0 ∧ t 0 ≤ c ∧ b ≤ t 1 ∧ t 1 ≤ c ∧
      c ≤ t 2 ∧ t 2 ≤ f ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2} ∧
    D a b c e f 1 = {t | b ≤ t 0 ∧ t 0 ≤ c ∧ c ≤ t 1 ∧ t 1 ≤ e ∧
      c ≤ t 2 ∧ t 2 ≤ e ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2} ∧
    D a b c e f 2 = {t | a ≤ t 0 ∧ t 0 ≤ b ∧ a ≤ t 1 ∧ t 1 ≤ b ∧
      e ≤ t 2 ∧ t 2 ≤ f ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2} ∧
    D a b c e f 3 = {t | a ≤ t 0 ∧ t 0 ≤ b ∧ b ≤ t 1 ∧ t 1 ≤ c ∧
      c ≤ t 2 ∧ t 2 ≤ f ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2} ∧
    D a b c e f 4 = {t | a ≤ t 0 ∧ t 0 ≤ b ∧ c ≤ t 1 ∧ t 1 ≤ f ∧
      c ≤ t 2 ∧ t 2 ≤ f ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2} ∧
    D a b c e f 5 = {t | b ≤ t 0 ∧ t 0 ≤ c ∧ c ≤ t 1 ∧ t 1 ≤ e ∧
      e ≤ t 2 ∧ t 2 ≤ f ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2} :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Wu2008DoubleSieve.LowerTripleContinuous

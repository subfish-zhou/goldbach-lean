import WR2GammaHighPairGeometry

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle Real Finset Filter Set MotherPair LiLiuPrereqBuchstab
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical Topology Interval

theorem rect_mem_iff {N : ℕ} {δ A B C D : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hB : B ≤ 10/23) (hD : D ≤ 10/23) (x : Gamma5ClassicalLabel) :
    x ∈ rectLabels N δ (windows j N) A B C D ↔
      x.1 ∈ boxConvolutionSupport (windows j N) ∧
      x.2 ∈ primePairs N ((N : ℝ)^(1/2-δ)/x.1) A B C D := by
  constructor
  · intro hx
    obtain ⟨hx, hp, hq, hpN, hqN, hpa, hpb, hqc, hqd, hpq⟩ := mem_filter.mp hx
    have hm := (mem_product.mp hx).1
    have hR := (support_local j hN hd hh hm).2.2.2
    refine ⟨hm, mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, hpq, hqd, hpN, hqN, hpb⟩⟩
    · exact (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N : ℝ)^(1/2-δ)/x.1) B)).mpr
        ⟨hp, hpa, hpb.le⟩
    · exact (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N : ℝ)^(1/2-δ)/x.1) D)).mpr
        ⟨hq, hqc, hqd.le⟩
  · rintro ⟨hm, hx⟩
    obtain ⟨hpair, hpq, hqd, hpN, hqN, hpb⟩ := mem_filter.mp hx
    obtain ⟨hpm, hqm⟩ := mem_product.mp hpair
    have hR := (support_local j hN hd hh hm).2.2.2
    obtain ⟨hp, hpa, _⟩ := (mem_primesIcc
      (rpow_nonneg (by linarith : 0 ≤ (N : ℝ)^(1/2-δ)/x.1) B)).mp hpm
    obtain ⟨hq, hqc, _⟩ := (mem_primesIcc
      (rpow_nonneg (by linarith : 0 ≤ (N : ℝ)^(1/2-δ)/x.1) D)).mp hqm
    have hpN' : x.2.1 ≤ N := by
      exact_mod_cast hpb.le.trans (cutoff_le_N j hN hd hh hm (by linarith : B ≤ 1))
    have hqN' : x.2.2 ≤ N := by
      exact_mod_cast hqd.le.trans (cutoff_le_N j hN hd hh hm (by linarith : D ≤ 1))
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hm, mem_product.mpr
      ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩⟩,
      hp, hq, hpN, hqN, hpa, hpb, hqc, hqd, hpq⟩

theorem sum_rect {N : ℕ} {δ A B C D : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hB : B ≤ 10/23) (hD : D ≤ 10/23) (f : Gamma5ClassicalLabel → ℝ) :
    (∑ x ∈ rectLabels N δ (windows j N) A B C D, f x) =
      ∑ d ∈ boxConvolutionSupport (windows j N),
        ∑ pq ∈ primePairs N ((N : ℝ)^(1/2-δ)/d) A B C D, f (d, pq) := by
  let P := fun d => primePairs N ((N : ℝ)^(1/2-δ)/d) A B C D
  have he : rectLabels N δ (windows j N) A B C D =
      (boxConvolutionSupport (windows j N)).biUnion (fun d => (P d).image (fun pq => (d, pq))) := by
    ext x
    rw [rect_mem_iff j hN hd hh hB hD, Finset.mem_biUnion]
    constructor
    · rintro ⟨hm, hx⟩
      exact ⟨x.1, hm, mem_image.mpr ⟨x.2, hx, Prod.eta x⟩⟩
    · rintro ⟨d, hm, hx⟩
      obtain ⟨pq, hpq, heq⟩ := mem_image.mp hx
      cases heq
      exact ⟨hm, hpq⟩
  have hdis : ∀ d ∈ boxConvolutionSupport (windows j N),
      ∀ e ∈ boxConvolutionSupport (windows j N), d ≠ e →
      Disjoint ((P d).image (fun pq => (d, pq))) ((P e).image (fun pq => (e, pq))) := by
    intro d _ e _ hde
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨pq, _, heq⟩ := mem_image.mp hx
    obtain ⟨rs, _, heq'⟩ := mem_image.mp hy
    exact hde (congrArg Prod.fst (heq.trans heq'.symm))
  rw [he, sum_biUnion hdis]
  apply sum_congr rfl
  intro d _
  exact sum_image (fun pq _ rs _ heq => congrArg Prod.snd heq)

theorem main_rect_identity {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ A B C D : ℝ, 1/5 ≤ A → B ≤ 10/23 → 1/5 ≤ C → D ≤ 10/23 →
      gamma5ClassicalMainMass N δ (windows j N) (rectLabels N δ (windows j N) A B C D) =
        4*logarithmicIntegral N*∑ d ∈ boxConvolutionSupport (windows j N),
          (convolutionCoeff (windows j N) d : ℝ)*
            gamma5MassOldWeight N d ((N : ℝ)^(1/2-δ))*
            arithmeticPairs (10/23) N d ((N : ℝ)^(1/2-δ)/d) A B C D := by
  have hβ := wuLocalExponent_pos 0 hd (by linarith : δ < 1/2)
  obtain ⟨T, hlarge⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < wuLocalExponent 0 δ*(1/5 : ℝ) by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN j A B C D hA hB hC hD
  have hN2 : 2 ≤ N := by omega
  unfold gamma5ClassicalMainMass
  rw [sum_rect j hN2 hd hh hB hD]
  congr 1
  apply sum_congr rfl
  intro d hm
  have hg := support_local j hN2 hd hh hm
  have hZ : (N : ℝ)^(wuLocalExponent 0 δ*(1/5 : ℝ)) ≤
      ((N : ℝ)^(1/2-δ)/d)^(1/5 : ℝ) := by
    rw [rpow_mul (Nat.cast_nonneg _)]
    exact rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg _) _) hg.2.2.1 (by norm_num)
  rw [arithmeticPairs, mul_sum]
  apply sum_congr rfl
  intro pq hpq
  obtain ⟨hpair, _, _, hpN, hqN, _⟩ := mem_filter.mp hpq
  obtain ⟨hp, hq⟩ := mem_product.mp hpair
  have hpc := (gamma5Mass_coordinate_mem_iff hg.2.2.2 pq.1).mp hp
  have hqc := (gamma5Mass_coordinate_mem_iff hg.2.2.2 pq.2).mp hq
  have hp4 := (hlarge N (by omega)).trans (MotherPair.prime_lower hg.2.2.2 hA hZ pq.1 hp).2
  have hq4 := (hlarge N (by omega)).trans (MotherPair.prime_lower hg.2.2.2 hC hZ pq.2 hq).2
  have hp2 : 2 < pq.1 := by exact_mod_cast (show (2 : ℝ) < pq.1 by linarith)
  have hq2 : 2 < pq.2 := by exact_mod_cast (show (2 : ℝ) < pq.2 by linarith)
  have hid := gamma5Mass_two_insertions (by omega : 0 < N) hg.1 hpc.1 hqc.1 hp2 hq2 hpN hqN hg.2.2.2
  have hH := clipH_eq (hpc.2.2.trans hB) (hqc.2.2.trans hD)
  dsimp only [gamma5ClassicalProduct]
  simp only [Nat.cast_mul]
  rw [mul_div_assoc, hid, hH]
  ring

theorem rectangle_mass {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ A B C D : ℝ, 1/5 ≤ A → A ≤ B → B ≤ 10/23 →
      1/5 ≤ C → C ≤ D → D ≤ 10/23 →
      |gamma5ClassicalMainMass N δ (windows j N) (rectLabels N δ (windows j N) A B C D) -
        rectIntegral A B C D*theta j N δ| ≤ ε*theta j N δ := by
  have hβ := wuLocalExponent_pos 0 hd (by linarith : δ < 1/2)
  have hα : 0 < wuLocalExponent 0 δ*(1/5 : ℝ) := by positivity
  obtain ⟨T1, hmass⟩ := eventually_atTop.mp
    (arithmetic_pair_uniform (a := (1/5 : ℝ)) (U := (10/23 : ℝ)) (by norm_num)
      (by norm_num) hα hβ le_rfl heps)
  obtain ⟨T2, hT24, hid⟩ := main_rect_identity hd hh
  refine ⟨max T1 T2, hT24.trans (le_max_right _ _), ?_⟩
  intro N hN j A B C D hA hAB hB hC hCD hD
  have hN4 : 4 ≤ N := by omega
  let W := windows j N
  let Q := (N : ℝ)^(1/2-δ)
  let w := fun d => (convolutionCoeff W d : ℝ)*gamma5MassOldWeight N d Q
  let J := rectIntegral A B C D
  let P := fun d => arithmeticPairs (10/23) N d (Q/d) A B C D
  have hw : ∀ d ∈ boxConvolutionSupport W, 0 ≤ w d := by
    intro d hm
    have hg := support_local j (by omega) hd hh hm
    apply mul_nonneg (Nat.cast_nonneg _)
    exact div_nonneg (wuSingularSeries_pos _ (Nat.mul_pos hg.1 (by omega))).le
      (mul_nonneg (Nat.cast_nonneg _) (log_pos hg.2.2.2).le)
  have hp : ∀ d ∈ boxConvolutionSupport W, |P d-J| ≤ ε := by
    intro d hm
    exact (hmass N (by omega) (Q/d) (support_local j (by omega) hd hh hm).2.2.1
      d A B C D hA hAB hB hC hCD hD).le
  have hsum : |(∑ d ∈ boxConvolutionSupport W, w d*P d) - J*∑ d ∈ boxConvolutionSupport W, w d| ≤
      ε*∑ d ∈ boxConvolutionSupport W, w d := by
    rw [mul_sum, ← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro d hm
    rw [show w d*P d-J*w d = w d*(P d-J) by ring, abs_mul, abs_of_nonneg (hw d hm)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hp d hm) (hw d hm)
  have hli : 0 ≤ 4*logarithmicIntegral N := mul_nonneg (by norm_num)
    (MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast (show 2 ≤ N by omega)))
  rw [hid N (by omega) j A B C D hA hB hC hD]
  unfold theta
  rw [gamma5Mass_theta_eq]
  change |4*logarithmicIntegral N*(∑ d ∈ boxConvolutionSupport W, w d*P d) -
    J*(4*logarithmicIntegral N*∑ d ∈ boxConvolutionSupport W, w d)| ≤
    ε*(4*logarithmicIntegral N*∑ d ∈ boxConvolutionSupport W, w d)
  rw [show 4*logarithmicIntegral N*(∑ d ∈ boxConvolutionSupport W, w d*P d) -
      J*(4*logarithmicIntegral N*∑ d ∈ boxConvolutionSupport W, w d) =
      4*logarithmicIntegral N*((∑ d ∈ boxConvolutionSupport W, w d*P d) -
        J*∑ d ∈ boxConvolutionSupport W, w d) by ring, abs_mul, abs_of_nonneg hli]
  exact (mul_le_mul_of_nonneg_left hsum hli).trans_eq (mul_left_comm _ _ _)

theorem term_mass {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ i : Term,
      |gamma5ClassicalMainMass N δ (windows j N)
          (termLabels (Wu04RemainingCore.row j) i N δ (windows j N)) -
        classicalIntegral (Wu04RemainingCore.row j) i*theta j N δ| ≤ ε*theta j N δ := by
  obtain ⟨T, hT4, hm⟩ := rectangle_mass hd hh heps
  refine ⟨T, hT4, ?_⟩
  intro N hN j i
  have hg := row_analytic j
  obtain ⟨_, hab, hbc, hce, _, _⟩ := parameter_order hg
  have ha : (1/5 : ℝ) ≤ 1/(Wu04RemainingCore.row j).S :=
    one_div_le_one_div_of_le (by linarith [hg.three_le_S]) hg.S_le_five
  have he : 1/(Wu04RemainingCore.row j).kappa3 ≤ (10/23 : ℝ) := by
    have hr : ∀ j : Fin 3, 1/(Wu04RemainingCore.row j).kappa3 ≤ (10/23 : ℝ) := by
      simp only [Wu04RemainingCore.row, ActualNineFeedback.coupledRow,
        SecondFunctionalPositive.parameters, Fin.forall_fin_succ, Fin.forall_fin_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, and_true]
      norm_num [SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
        SecondFunctionalParameters.row4]
    exact hr j
  cases i with
  | gammaFive =>
    exact hm N hN j _ _ _ _ ha (hab.trans hbc.le) (hce.le.trans he)
      ha (hab.trans hbc.le) (hce.le.trans he)
  | gammaSix =>
    exact hm N hN j _ _ _ _ ha hab (hbc.le.trans (hce.le.trans he))
      (ha.trans (hab.trans hbc.le)) hce.le he
  | gammaSeven =>
    exact hm N hN j _ _ _ _ ha hab (hbc.le.trans (hce.le.trans he))
      ha hab (hbc.le.trans (hce.le.trans he))
  | gammaEight =>
    exact hm N hN j _ _ _ _ ha hab (hbc.le.trans (hce.le.trans he))
      (ha.trans hab) hbc.le (hce.le.trans he)

#check @rect_mem_iff
#check @sum_rect
#check @main_rect_identity
#check @rectangle_mass
#check @term_mass
#print axioms rect_mem_iff
#print axioms sum_rect
#print axioms main_rect_identity
#print axioms rectangle_mass
#print axioms term_mass
end WuPaper.R2GammaHigh

import WR2GammaHighTheta

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle Real Finset MotherPair
open scoped Classical

theorem support_local {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hm : d ∈ boxConvolutionSupport (windows j N)) :
    0 < d ∧ d ≤ N ∧
      (N : ℝ)^(wuLocalExponent 0 δ) ≤ (N : ℝ)^(1/2-δ)/d ∧
      1 < (N : ℝ)^(1/2-δ)/d := by
  rw [support_eq] at hm
  have hg := prime_geometry j hN hd hh hm
  have hr := seven_ratio_geometry (j.castAdd 4) hN hd hh hm
  refine ⟨hg.2.2.2.1, hg.2.2.2.2.1, ?_, hr.1⟩
  have hδ : wuLocalExponent 0 δ ≤ δ := by
    simpa only [wuLocalExponent, zero_add, pow_one] using
      (min_le_left δ (1/2-δ))
  have ht := (interval_geometry j).2.2.1
  exact (rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega))
    (by dsimp [levelExponent]; linarith :
      wuLocalExponent 0 δ ≤ levelExponent δ-psiRight (j.castAdd 4))).trans hr.2.2

theorem cutoff_le_N {N d : ℕ} {δ x : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hm : d ∈ boxConvolutionSupport (windows j N)) (hx : x ≤ 1) :
    ((N : ℝ)^(1/2-δ)/d)^x ≤ N := by
  have hg := support_local j hN hd hh hm
  have hQ : 0 ≤ (N : ℝ)^(1/2-δ) := rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ ((N : ℝ)^(1/2-δ)/d)^1 := rpow_le_rpow_of_exponent_le hg.2.2.2.le hx
    _ = (N : ℝ)^(1/2-δ)/d := rpow_one _
    _ ≤ (N : ℝ)^(1/2-δ) := div_le_self hQ (by exact_mod_cast hg.1)
    _ ≤ (N : ℝ)^1 := rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
    _ = N := rpow_one _

theorem pair_geometry {S U : ℝ} (hcap : CapAdmissible S U)
    {N : ℕ} {δ : ℝ} (j : Fin 3) (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100)
    {x : Gamma5ClassicalLabel} (hx : x ∈ capLabels S U N δ (windows j N)) :
    ClassicalGeometry S U 0 N δ x := by
  have hS : 0 < S := by linarith [hcap.three_le_S]
  have hU : 0 < 1-2*U := by linarith [hcap.cap_lt_half]
  obtain ⟨hxambient, hp, hq, _hpN, _hqN, hzp, hpq, hqu⟩ := mem_filter.mp hx
  have hm := (mem_product.mp hxambient).1
  have hb := support_local j hN hd hh hm
  let R := (N : ℝ)^(1/2-δ)/x.1
  let L := gamma5ClassicalLevel N δ x
  let z := wuLocalCutoff N δ x.1 S
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hβ := wuLocalExponent_pos 0 hd (by linarith : δ < 1/2)
  have hR : 1 < R := hb.2.2.2
  have hR0 : 0 < R := by linarith
  have hp0 : (0 : ℝ) < x.2.1 := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < x.2.2 := by exact_mod_cast hq.pos
  have hpq' : (x.2.1 : ℝ) ≤ x.2.2 := by exact_mod_cast hpq.le
  have hLdef : L = R/((x.2.1 : ℝ)*x.2.2) := by
    dsimp [L, R, gamma5ClassicalLevel, gamma5ClassicalProduct]
    push_cast
    ring
  have hpair := classical_pair_geometry hcap hR hp0 hq0 hzp hpq' hqu.le
  rw [← hLdef] at hpair
  have hL : 1 < L := (one_lt_rpow hR hU).trans_le hpair.1
  have hz : 1 < z := one_lt_rpow hR (by positivity)
  have hbridge := classical_ratio2_cutoff_bridge hL hz
    (hpair.2.2.trans (by linarith [hcap.S_le_five]))
  have hM : 0 < gamma5ClassicalProduct x := Nat.mul_pos (Nat.mul_pos hb.1 hp.pos) hq.pos
  have hM0 : (0 : ℝ) < gamma5ClassicalProduct x := by exact_mod_cast hM
  have hMN : (gamma5ClassicalProduct x : ℝ) ≤ N := by
    have hMQ : (gamma5ClassicalProduct x : ℝ) ≤ (N : ℝ)^(1/2-δ) := by
      have h := (lt_div_iff₀ hM0).mp hL
      linarith
    exact hMQ.trans (by simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le hN1.le (show 1/2-δ ≤ 1 by linarith))
  have hpow (e : ℝ) (he : 0 ≤ e) : (N : ℝ)^(wuLocalExponent 0 δ*e) ≤ R^e := by
    rw [rpow_mul hN0.le]
    exact rpow_le_rpow (rpow_nonneg hN0.le _) hb.2.2.1 he
  have hprime : (N : ℝ)^(classicalAlpha S 0 δ) ≤ (x.2.1 : ℝ) := by
    calc
      _ ≤ (N : ℝ)^(wuLocalExponent 0 δ*(1/S)) := by
        apply rpow_le_rpow_of_exponent_le hN1.le
        unfold classicalAlpha
        apply (div_le_iff₀ (mul_pos (by norm_num) hS)).mpr
        have he : wuLocalExponent 0 δ*(1/S)*(2*S) = 2*wuLocalExponent 0 δ := by field_simp
        rw [he]
        linarith
      _ ≤ R^(1/S) := hpow _ (by positivity)
      _ ≤ _ := hzp
  have hcut : (N : ℝ)^(classicalZeta S U 0 δ) ≤ min z (sqrt L) := by
    apply le_min
    · calc
        _ ≤ (N : ℝ)^(wuLocalExponent 0 δ*(1/S)) :=
          rpow_le_rpow_of_exponent_le hN1.le
            (mul_le_mul_of_nonneg_left (min_le_left _ _) hβ.le)
        _ ≤ z := hpow _ (by positivity)
    · calc
        _ ≤ (N : ℝ)^(wuLocalExponent 0 δ*((1-2*U)/2)) :=
          rpow_le_rpow_of_exponent_le hN1.le
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hβ.le)
        _ ≤ R^((1-2*U)/2) := hpow _ (by positivity)
        _ = sqrt (R^(1-2*U)) := by
          rw [sqrt_eq_rpow, ← rpow_mul hR0.le]
          congr 1
          ring
        _ ≤ sqrt L := sqrt_le_sqrt hpair.1
  exact ⟨hM, hMN, hL, hbridge.1, hbridge.2.1, hcut, hprime,
    hbridge.2.2.1, hbridge.2.2.2.1, hbridge.2.2.2.2, hpair.2.1, hpair.2.2⟩

theorem rect_labels_subset_cap {S U B C D : ℝ} (hDU : D ≤ U)
    {N : ℕ} {δ : ℝ} (j : Fin 3) (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    rectLabels N δ (windows j N) (1/S) B C D ⊆ capLabels S U N δ (windows j N) := by
  intro x hx
  obtain ⟨hx, hp, hq, hpN, hqN, hpa, _hpb, _hqc, hqd, hpq⟩ := mem_filter.mp hx
  have hR := (support_local j hN hd hh (mem_product.mp hx).1).2.2.2
  exact mem_filter.mpr ⟨hx, hp, hq, hpN, hqN, hpa, hpq,
    hqd.trans_le (rpow_le_rpow_of_exponent_le hR.le hDU)⟩

theorem term_labels_subset_cap {N : ℕ} {δ : ℝ} (j : Fin 3) (i : Term)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    termLabels (Wu04RemainingCore.row j) i N δ (windows j N) ⊆
      capLabels (Wu04RemainingCore.row j).S (1/(Wu04RemainingCore.row j).kappa3)
        N δ (windows j N) := by
  obtain ⟨_, _, hbc, hce, _, _⟩ := parameter_order (row_analytic j)
  cases i with
  | gammaFive => exact rect_labels_subset_cap hce.le j hN hd hh
  | gammaSix => exact rect_labels_subset_cap le_rfl j hN hd hh
  | gammaSeven => exact rect_labels_subset_cap (hbc.le.trans hce.le) j hN hd hh
  | gammaEight => exact rect_labels_subset_cap hce.le j hN hd hh

theorem high_cutoffs {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hm : d ∈ boxConvolutionSupport (windows j N)) :
    wuLocalCutoff N δ d (Wu04RemainingCore.row j).S ≤
      wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa1 ∧
    wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa1 ≤
      wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa2 ∧
    wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa2 ≤
      wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa3 ∧
    wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa3 ≤
      wuLocalCutoff N δ d (Wu04RemainingCore.row j).s := by
  have hg := row_analytic j
  have hq := (support_local j hN hd hh hm).2.2.2.le
  have hs : 0 < (Wu04RemainingCore.row j).s := by linarith [hg.two_lt_s]
  have h3 := hg.mother.s_le_kappa3
  have h2 := hg.mother.kappa3_lt_kappa2.le
  have h1 := hg.mother.kappa2_lt_kappa1.le
  exact ⟨high_cutoff_antitone hq (hs.trans_le (h3.trans (h2.trans h1))) hg.mother.kappa1_le_S,
    high_cutoff_antitone hq (hs.trans_le (h3.trans h2)) h1,
    high_cutoff_antitone hq (hs.trans_le h3) h2, high_cutoff_antitone hq hs h3⟩

theorem term_count_original {N : ℕ} {δ : ℝ} (j : Fin 3) (i : Term)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    termCount (Wu04RemainingCore.row j) i N δ (windows j N)
      (termLabels (Wu04RemainingCore.row j) i N δ (windows j N)) = gamma j N δ i.index := by
  obtain ⟨_, _, hbc, hce, hef, hf⟩ := parameter_order (row_analytic j)
  have hb1 : 1/(Wu04RemainingCore.row j).kappa1 ≤ 1 := by linarith
  have hc1 : 1/(Wu04RemainingCore.row j).kappa2 ≤ 1 := by linarith
  have he1 : 1/(Wu04RemainingCore.row j).kappa3 ≤ 1 := by linarith
  have hB := fun d hm => cutoff_le_N j hN hd hh (d := d) hm hb1
  have hC := fun d hm => cutoff_le_N j hN hd hh (d := d) hm hc1
  have hE := fun d hm => cutoff_le_N j hN hd hh (d := d) hm he1
  unfold gamma
  cases i with
  | gammaFive =>
    simp only [termCount, termLabels, fixedCount, Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hC hC]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d _
    rw [secondFunctionalMotherGamma, fourthRowMotherPair, sum_comm]
    simp only [mul_sum, mul_ite, mul_zero, wuLocalCutoff, gamma5ClassicalProduct]
  | gammaSix =>
    simp only [termCount, termLabels, fixedCount, Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hB hE]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d _
    rw [secondFunctionalMotherGamma, fourthRowMotherPair, sum_comm]
    simp only [mul_sum, mul_ite, mul_zero, wuLocalCutoff, gamma5ClassicalProduct]
  | gammaSeven =>
    simp only [termCount, termLabels, Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hB hB]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d hm
    have hc := high_cutoffs j hN hd hh hm
    rw [raw_seven N d N (hc.2.1.trans (hc.2.2.1.trans hc.2.2.2))]
    simp only [mul_sum, mul_ite, mul_zero, wuLocalCutoff, gamma5ClassicalProduct]
  | gammaEight =>
    simp only [termCount, termLabels, Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hB hC]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d hm
    have hc := high_cutoffs j hN hd hh hm
    rw [raw_eight N d N hc.1 (hc.2.1.trans (hc.2.2.1.trans hc.2.2.2))
      (hc.2.2.1.trans hc.2.2.2)]
    simp only [mul_sum, mul_ite, mul_zero, wuLocalCutoff, gamma5ClassicalProduct]

#check @support_local
#check @cutoff_le_N
#check @pair_geometry
#check @rect_labels_subset_cap
#check @term_labels_subset_cap
#check @high_cutoffs
#check @term_count_original
#print axioms support_local
#print axioms cutoff_le_N
#print axioms pair_geometry
#print axioms rect_labels_subset_cap
#print axioms term_labels_subset_cap
#print axioms high_cutoffs
#print axioms term_count_original
end WuPaper.R2GammaHigh

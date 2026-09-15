import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerClassical

/-!
# Fixed finite-grid gain on actual admissible two-prime boxes

The grid is frozen before the threshold. Both sorted square prefixes
are discharged from the admissible exponent geometry. Cutoff transfer
uses inclusion of actual strict source carriers.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem truncatedSixthLower_source_box {N : ℕ} {δ Δ x y : ℝ}
    (hN : 1 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 100)
    (hΔlo : 1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ)
    (hΔhi : Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ))
    (hxy : truncatedSixthLowerAdmissibleRegion δ x y) :
    wuSourceBox 2 δ N 2 Δ ![(N : ℝ) ^ y, (N : ℝ) ^ x] := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hyx : x ≤ y := hxy.1.2.1.trans hxy.1.2.2.1
  have hd := truncatedSixthLower_depth_two hδ hδhi
  refine ⟨le_rfl, hΔlo, hΔhi, ?_, ?_, ?_⟩
  · intro j k hjk
    fin_cases j <;> fin_cases k
    · exact le_rfl
    · exact rpow_le_rpow_of_exponent_le hNreal hyx
    · simp at hjk
    · exact le_rfl
  · intro j
    fin_cases j
    · exact rpow_le_rpow_of_exponent_le hNreal
        (hd.le.trans (hxy.1.1.trans hyx))
    · exact rpow_le_rpow_of_exponent_le hNreal (hd.le.trans hxy.1.1)
  · intro j
    fin_cases j
    · norm_num [Finset.prod_filter, Fin.prod_univ_two]
      change ((N : ℝ) ^ y) ^ 2 ≤ (N : ℝ) ^ (1 / 2 - δ)
      rw [← rpow_natCast, ← rpow_mul hN0]
      apply rpow_le_rpow_of_exponent_le hNreal
      change y * 2 ≤ truncatedSixthLowerC δ
      linarith [hxy.2]
    · norm_num [Finset.prod_filter, Fin.prod_univ_two]
      change (N : ℝ) ^ y * ((N : ℝ) ^ x) ^ 2 ≤ (N : ℝ) ^ (1 / 2 - δ)
      rw [← rpow_natCast, ← rpow_mul hN0, ← rpow_add (by linarith : (0 : ℝ) < N)]
      apply rpow_le_rpow_of_exponent_le hNreal
      have hm := truncatedSixthLower_parameters.2.2.2.2
      have hs := truncatedSixthLower_prefix_slack hxy.1
      change y + x * 2 ≤ truncatedSixthLowerC δ
      linarith

theorem truncatedSixthLower_box_cutoff {N d : ℕ} {δ x y t : ℝ}
    (hN : 1 < N) (hd : 0 < d) (ht : 0 < t)
    (hprod : (d : ℝ) ≤ (N : ℝ) ^ (x + y))
    (hs : t ≤ truncatedSixthLowerS δ x y) :
    (N : ℝ) ^ truncatedSixthLowerAlpha ≤ wuLocalCutoff N δ d t := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hα := truncatedSixthLower_parameters.1
  have hst : truncatedSixthLowerAlpha ≤ (truncatedSixthLowerC δ - (x + y)) / t := by
    apply (le_div_iff₀ ht).mpr
    have h := (le_div_iff₀ hα).mp hs
    linarith
  have hlevel : (N : ℝ) ^ (truncatedSixthLowerC δ - (x + y)) ≤
      (N : ℝ) ^ (1 / 2 - δ) / d := by
    rw [rpow_sub hN0]
    exact div_le_div_of_nonneg_left (rpow_nonneg hN0.le _) hd0 hprod
  calc
    _ ≤ (N : ℝ) ^ ((truncatedSixthLowerC δ - (x + y)) / t) :=
      rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) hst
    _ = ((N : ℝ) ^ (truncatedSixthLowerC δ - (x + y))) ^ (1 / t) := by
      rw [← rpow_mul hN0.le, div_eq_mul_inv, one_div]
    _ ≤ wuLocalCutoff N δ d t :=
      rpow_le_rpow (rpow_nonneg hN0.le _) hlevel (by positivity)

theorem truncatedSixthLower_source_count_cutoff {N p q : ℕ} {z Z : ℝ}
    (hp : p.Prime) (hq : q.Prime) (hzp : z ≤ (p : ℝ))
    (hzq : z ≤ (q : ℝ)) (hcut : z ≤ Z) :
    (sourceSieveCount N (p * q) ((p * q) * N) Z : ℝ) ≤
      (sieveCount N (p * q) N z : ℝ) := by
  have hcar : sourceSieveCarrier N (p * q) ((p * q) * N) Z ⊆
      sourceSieveCarrier N (p * q) ((p * q) * N) z := by
    intro r hr
    obtain ⟨hrange, hp, hd, hs⟩ := mem_filter.mp hr
    exact mem_filter.mpr ⟨hrange, hp, hd,
      fun a ha hcop haz => hs a ha hcop (haz.trans_le hcut)⟩
  rw [(truncatedSixthLower_carrier_bridge hp hq hzp hzq).1] at hcar
  unfold sourceSieveCount sieveCount
  exact_mod_cast Finset.card_le_card hcar

theorem truncatedSixthLower_box_phi_le {N : ℕ} {δ Δ x y t : ℝ}
    (hN : 1 < N) (ht : 0 < t)
    (hplo : (N : ℝ) ^ truncatedSixthLowerAlpha ≤ (N : ℝ) ^ x / Δ)
    (hqlo : (N : ℝ) ^ truncatedSixthLowerAlpha ≤ (N : ℝ) ^ y / Δ)
    (hs : t ≤ truncatedSixthLowerS δ x y) :
    wuBoxPhi N δ (convolutionWuWindows N Δ ![(N : ℝ) ^ y, (N : ℝ) ^ x]) t ≤
      ∑ b ∈ primeWindow N ((N : ℝ) ^ y / Δ) ((N : ℝ) ^ y) ×ˢ
        primeWindow N ((N : ℝ) ^ x / Δ) ((N : ℝ) ^ x),
          (sieveCount N (b.1 * b.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  have hW : convolutionWuWindows N Δ ![(N : ℝ) ^ y, (N : ℝ) ^ x] =
      ![primeWindow N ((N : ℝ) ^ y / Δ) ((N : ℝ) ^ y),
        primeWindow N ((N : ℝ) ^ x / Δ) ((N : ℝ) ^ x)] := by
    funext j
    fin_cases j <;> rfl
  rw [hW]
  unfold wuBoxPhi convolutionSieveCount
  change (∑ d ∈ boxConvolutionSupport _, _) ≤ _
  rw [truncatedSixthLower_two_window_sum]
  apply sum_le_sum
  intro b hb
  obtain ⟨hq, hp⟩ := mem_product.mp hb
  have hq' := mem_primeWindow.mp hq
  have hp' := mem_primeWindow.mp hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprod : (b.1 * b.2 : ℕ) ≤ (N : ℝ) ^ (x + y) := by
    rw [Nat.cast_mul, add_comm x y, rpow_add hN0]
    exact mul_le_mul hq'.2.2.2.le hp'.2.2.2.le (Nat.cast_nonneg _) (rpow_nonneg hN0.le _)
  exact truncatedSixthLower_source_count_cutoff hq'.1 hp'.1
    (hqlo.trans hq'.2.2.1) (hplo.trans hp'.2.2.1)
    (truncatedSixthLower_box_cutoff hN (mul_pos hq'.1.pos hp'.1.pos) ht hprod hs)

theorem truncatedSixthLower_finite_grid_gain {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hη : 0 < η)
    (G : Finset ℝ) (hG : ∀ t ∈ G, 2 ≤ t ∧ t ≤ 5) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ x y : ℝ,
      1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
      Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
      truncatedSixthLowerAdmissibleRegion δ x y →
      (N : ℝ) ^ truncatedSixthLowerAlpha ≤ (N : ℝ) ^ x / Δ →
      (N : ℝ) ^ truncatedSixthLowerAlpha ≤ (N : ℝ) ^ y / Δ →
      ∀ t ∈ G, t ≤ truncatedSixthLowerS δ x y →
      (wuLowerCoefficient t + wuImprovementLimit false δ t - η) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
            (convolutionWuWindows N Δ ![(N : ℝ) ^ y, (N : ℝ) ^ x]) ≤
        ∑ b ∈ primeWindow N ((N : ℝ) ^ y / Δ) ((N : ℝ) ^ y) ×ˢ
          primeWindow N ((N : ℝ) ^ x / Δ) ((N : ℝ) ^ x),
            (sieveCount N (b.1 * b.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  have hmem (t : G) : ∃ T : ℕ,
      wuImprovementLimit false δ t - η ∈ wuAdmissibleImprovements false 2 δ t T := by
    exact wuImprovementLimit_sub_mem false 1 hδ (by linarith)
      (by linarith [(hG t t.2).1]) (by linarith [(hG t t.2).2]) hη
  choose T hT using hmem
  refine ⟨max 4 (univ.sup T), le_max_left _ _, ?_⟩
  intro N hN he Δ x y hΔlo hΔhi hxy hplo hqlo t ht hs
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hTN : T ⟨t, ht⟩ ≤ N :=
    (le_sup (f := T) (mem_univ ⟨t, ht⟩)).trans ((le_max_right _ _).trans hN)
  have hbox := truncatedSixthLower_source_box (by omega) hδ hδhi hΔlo hΔhi hxy
  have hgain := hT ⟨t, ht⟩ N hTN hN4 he 2 Δ
    ![(N : ℝ) ^ y, (N : ℝ) ^ x] hbox
  simp only [wuImprovementComparison, Bool.false_eq_true, if_false] at hgain
  rw [← add_sub_assoc] at hgain
  exact hgain.trans (truncatedSixthLower_box_phi_le (by omega)
    (by linarith [(hG t ht).1]) hplo hqlo hs)

end Wu2008DoubleSieve

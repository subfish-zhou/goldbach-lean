import Wu08RecoveryInterior

noncomputable section
open Finset Real Set LiLiuPrereqBuchstab
open scoped Classical
open Wu2008DoubleSieve
namespace Wu08FirstPrimeFour.SmallBoundaryRecovery
open FourRoughClosedMass SmallGrid SmallBoundary

theorem reciprocal_union_le (S T : Finset SmallGrid.Quad) :
    reciprocalMass (S ∪ T) ≤ reciprocalMass S+reciprocalMass T := by
  have he := sum_inter_add_sum_sdiff (S ∪ T) S (fun q => 1/(fourModulusProduct q : ℝ))
  have hi : (S ∪ T) ∩ S = S := by ext q; simp
  rw [hi] at he
  have hs : (S ∪ T) \ S ⊆ T := by
    intro q hq
    exact (mem_union.mp (mem_sdiff.mp hq).1).resolve_left (mem_sdiff.mp hq).2
  have ht := sum_le_sum_of_subset_of_nonneg hs (f := fun q => 1/(fourModulusProduct q : ℝ))
    (by intros; positivity)
  unfold reciprocalMass
  linarith only [he,ht]

theorem effective_term_bound {N : ℕ} {e : Bool} {ρ s : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ) (hs : log ρ/log N ≤ s)
    (hlo : 2*s ≤ FourRoughClosedMass.alpha-1/15)
    (hhi : 1/10+s ≤ FourRoughClosedMass.beta)
    (htop : lam-FourRoughClosedMass.alpha+2*s ≤ 1/3)
    {q : SmallGrid.Quad} (hq : q ∈ effectiveQuads N e ρ) :
    0 ≤ unshiftedTerm N q ∧ unshiftedTerm N q ≤ 120/(fourModulusProduct q : ℝ) := by
  obtain ⟨hr,hw⟩ := mem_filter.mp hq
  obtain ⟨_,hy,_,_,hu⟩ := relaxed_low hN hρ hs hlo hhi htop hr hw
  have hy0 : 0 < coord N q.2.1 := by linarith [hy.1]
  have hω := buchstab_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans hu)
  have hωu := buchstab_le_one ((by norm_num : (1 : ℝ) ≤ 2).trans hu)
  have hd : 0 ≤ density (coord N q.1) (coord N q.2.1) (coord N q.2.2.1) (coord N q.2.2.2) :=
    div_nonneg hω hy0.le
  have hdu : density (coord N q.1) (coord N q.2.1) (coord N q.2.2.1) (coord N q.2.2.2) ≤ 15 := by
    apply (div_le_iff₀ hy0).mpr
    linarith [hy.1]
  refine ⟨div_nonneg (mul_nonneg (atomWeight_nonneg _ _) hd) (Nat.cast_nonneg _),?_⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (mul_le_mul (atomWeight_le_eight N q.1) hdu hd (by norm_num)).trans_eq (by norm_num)

theorem actual_three_band_cover {N : ℕ} {e : Bool} {ρ s : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ) (hs : log ρ/log N ≤ s)
    (hlo : 2*s ≤ FourRoughClosedMass.alpha-1/15)
    (hhi : 1/10+s ≤ FourRoughClosedMass.beta)
    (htop : lam-FourRoughClosedMass.alpha+2*s ≤ 1/3) :
    effectiveQuads N e ρ \ smallClosed N e ⊆
      (firstBand N (FourRoughClosedMass.alpha-s) FourRoughClosedMass.alpha ∪
        firstBand N (1/10) (1/10+s)) ∪ orderBand N s := by
  intro q hq
  obtain ⟨hq,hnot⟩ := mem_sdiff.mp hq
  have hb := effective_subset_box hN hρ hs hlo hhi htop hq
  obtain ⟨hr,hw⟩ := mem_filter.mp hq
  obtain ⟨_,_,_,_,ha,hu,hab,_,_,_,_⟩ := relaxed_coordinates hN hρ hr hw
  by_cases hl : FourRoughClosedMass.alpha ≤ coord N q.1
  · by_cases hh : coord N q.1 ≤ 1/10
    · have hn : ¬ coord N q.1 ≤ coord N q.2.1 := fun h => hnot (interior_mem hN hρ hq hl hh h)
      exact mem_union_right _ (mem_filter.mpr ⟨hb,(le_of_not_ge hn),by linarith⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hb,le_of_not_ge hh,by linarith⟩))
  · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hb,by linarith,le_of_not_ge hl⟩))

/-- Actual effective support, all three closed boundary bands, and the literal
small weight. No diagonal or prime endpoint atom is removed. -/
theorem unshiftedMass_Q_paid {N : ℕ} {e : Bool} {ρ s ε : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ) (hs : log ρ/log N ≤ s)
    (hlo : 2*s ≤ FourRoughClosedMass.alpha-1/15)
    (hhi : 1/10+s ≤ FourRoughClosedMass.beta)
    (htop : lam-FourRoughClosedMass.alpha+2*s ≤ 1/3)
    (hm : windowMass N ≤ 5) (hε : 0 ≤ ε)
    (hstrip : ∀ a b : ℝ, a ∈ low → b ∈ low → a ≤ b →
      (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b), 1/(p : ℝ)) ≤ 15*(b-a)+ε) :
    unshiftedMass N e ρ ≤ SmallQuadrature.Q N e+45000*(15*s+ε) := by
  have hn : 1 < N := by exact_mod_cast (show (1 : ℝ) < N by linarith)
  have hs0 : 0 ≤ s := (div_nonneg (log_nonneg hρ.le) (log_nonneg (by linarith))).trans hs
  have hal : FourRoughClosedMass.alpha-s ∈ low :=
    ⟨by linarith,by linarith [alpha_low.2]⟩
  have hbu : (1/10 : ℝ)+s ∈ low :=
    ⟨by linarith, hhi.trans beta_low.2⟩
  have h1 := firstBand_paid hn hm hε (show FourRoughClosedMass.alpha-s ≤ FourRoughClosedMass.alpha by linarith)
    (hstrip _ _ hal alpha_low (by linarith))
  have h2 := firstBand_paid hn hm hε (show (1/10 : ℝ) ≤ 1/10+s by linarith)
    (hstrip _ _ Large.cutoff_geometry.2 hbu (by linarith))
  have h3 := orderBand_paid hn hm hs0 hε hstrip
  let D := effectiveQuads N e ρ \ smallClosed N e
  have hb : reciprocalMass D ≤ 375*(15*s+ε) := by
    have hsub := sum_le_sum_of_subset_of_nonneg
      (actual_three_band_cover (e := e) hN hρ hs hlo hhi htop) (f := fun q => 1/(fourModulusProduct q : ℝ))
      (by intros; positivity)
    have hu := reciprocal_union_le
      (firstBand N (FourRoughClosedMass.alpha-s) FourRoughClosedMass.alpha ∪ firstBand N (1/10) (1/10+s)) (orderBand N s)
    have hu' := reciprocal_union_le (firstBand N (FourRoughClosedMass.alpha-s) FourRoughClosedMass.alpha)
      (firstBand N (1/10) (1/10+s))
    have hsub' : reciprocalMass D ≤ _ := hsub.trans hu
    linarith only [hsub',hu',h1,h2,h3]
  have hd : (∑ q ∈ D, unshiftedTerm N q) ≤ 120*reciprocalMass D := by
    rw [reciprocalMass,mul_sum]
    apply sum_le_sum
    intro q hq
    simpa only [mul_one_div] using (effective_term_bound hN hρ hs hlo hhi htop (mem_sdiff.mp hq).1).2
  have hi : (∑ q ∈ effectiveQuads N e ρ ∩ smallClosed N e, unshiftedTerm N q) ≤ SmallQuadrature.Q N e := by
    rw [← smallClosed_eq_Q hn e]
    exact sum_le_sum_of_subset_of_nonneg (inter_subset_right) (fun q hq _ => smallClosed_nonneg hn hq)
  have he := sum_inter_add_sum_sdiff (effectiveQuads N e ρ) (smallClosed N e) (unshiftedTerm N)
  change _+ (∑ q ∈ D, unshiftedTerm N q) = unshiftedMass N e ρ at he
  linarith only [hi,hd,hb,he]

theorem unshiftedMass_I_paid {s ε : ℝ} (_hs0 : 0 ≤ s) (hε : 0 < ε)
    (hlo : 2*s ≤ FourRoughClosedMass.alpha-1/15)
    (hhi : 1/10+s ≤ FourRoughClosedMass.beta)
    (htop : lam-FourRoughClosedMass.alpha+2*s ≤ 1/3) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool, ∀ ρ : ℝ,
      1 < ρ → log ρ/log N ≤ s →
      unshiftedMass N e ρ ≤ SmallQuadrature.I e+ε+45000*(15*s+ε) := by
  obtain ⟨T1,hT1,h1⟩ := closed_strip_uniform hε
  obtain ⟨T2,_,h2⟩ := windowMass_uniform
  obtain ⟨T3,_,h3⟩ := SmallQuadrature.weighted_quadrature hε
  refine ⟨max T1 (max T2 T3),hT1.trans (le_max_left _ _),?_⟩
  intro N hN e ρ hρ hs
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
  have hb := unshiftedMass_Q_paid (e := e) hn4 hρ hs hlo hhi htop (h2 N (by omega)) hε.le (h1 N (by omega))
  have hq := (abs_lt.mp (h3 N (by omega) e)).2
  linarith only [hb,hq]

#check reciprocal_union_le
#print axioms reciprocal_union_le
#check effective_term_bound
#print axioms effective_term_bound
#check actual_three_band_cover
#print axioms actual_three_band_cover
#check unshiftedMass_Q_paid
#print axioms unshiftedMass_Q_paid
#check unshiftedMass_I_paid
#print axioms unshiftedMass_I_paid
end Wu08FirstPrimeFour.SmallBoundaryRecovery

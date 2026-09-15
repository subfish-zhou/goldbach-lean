import MathlibNt.Wu2008DoubleSieve.Gamma16Quotient
import MathlibNt.Wu2008DoubleSieve.Gamma16Geometry
import MathlibNt.Wu2008DoubleSieve.Omega3Relative

/-! # Actual finite switching, with bad-d and exceptional prime outputs retained -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

abbrev Gamma16OutputLabel := Σ _ : Gamma16Tuple, ℕ

noncomputable def gamma16OutputLabels (N : ℕ) (δ : ℝ) (d : ℕ) :
    Finset Gamma16OutputLabel :=
  (gamma16Tuples N δ d).sigma (gamma16PrefixCarrier N d)

noncomputable def gamma16BadCount {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    (((gamma16OutputLabels N δ d).filter (fun a => Omega3BadD N d a.2)).card : ℝ)

noncomputable def gamma16ExceptionalCount {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    (((gamma16OutputLabels N δ d).filter
      (fun a => a.2 ∈ omega3ExceptionalOutputs N δ)).card : ℝ)

theorem gamma16_output_label_injective :
    Function.Injective (fun a : Gamma16OutputLabel => (a.2, a.1)) := by
  rintro ⟨p, l⟩ ⟨p', l'⟩ h
  have hp : p = p' := congrArg Prod.snd h
  have hl : l = l' := congrArg Prod.fst h
  subst p'; subst l'
  rfl

theorem gamma16_output_lt {N d : ℕ} {δ : ℝ} (hN : 4 ≤ N) (he : Even N)
    {a : Gamma16OutputLabel} (ha : a ∈ gamma16OutputLabels N δ d) : a.2 < N := by
  have hm := mem_filter.mp (mem_sigma.mp ha).2
  exact omega3_prime_output_lt hN he hm.2.1 (Nat.le_of_lt_succ (mem_range.mp hm.1))

theorem gamma16_selected_large {N d : ℕ} {δ η : ℝ}
    (hl : (N : ℝ) ^ η ≤ wuLocalCutoff N δ d (291 / 100))
    {a : Gamma16OutputLabel} (ha : a ∈ gamma16OutputLabels N δ d) (j : Fin 4) :
    (a.1 j).Prime ∧ a.1 j ∣ N - a.2 ∧ (N : ℝ) ^ η ≤ (a.1 j : ℝ) := by
  obtain ⟨hp, hell⟩ := mem_sigma.mp ha
  have h := (mem_gamma16Tuples.mp hp).1 j
  have hd : a.1 j ∣ d * gamma16Product a.1 := by
    have hp : gamma16Product a.1 = ∏ j : Fin 4, a.1 j := by
      simp [gamma16Product, Fin.prod_univ_succ, mul_assoc]
    rw [hp]
    exact dvd_mul_of_dvd_right (dvd_prod_of_mem a.1 (mem_univ j)) d
  exact ⟨h.1, hd.trans (mem_filter.mp hell).2.2.1, hl.trans h.2.2.1⟩

theorem gamma16_good_labels_le {i N d : ℕ} {δ Z : ℝ} {W : Fin i → Finset ℕ}
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (hdW : d ∈ boxConvolutionSupport W) :
    (((gamma16OutputLabels N δ d).filter
      (fun a => ¬Omega3BadD N d a.2 ∧ ¬a.2 ∣ N ∧ Z ≤ (a.2 : ℝ))).card : ℝ) ≤
      ∑ c ∈ (gamma16Profiles N δ W).filter (fun c => c.1 = d),
        (((gamma16PrimeFibre N δ c).filter
          (fun p => Sifted N (N - gamma16Cofactor c * p) Z)).card : ℝ) := by
  let S := (gamma16OutputLabels N δ d).filter
    (fun a => ¬Omega3BadD N d a.2 ∧ ¬a.2 ∣ N ∧ Z ≤ (a.2 : ℝ))
  let T := ((gamma16Profiles N δ W).filter (fun c => c.1 = d)).sigma fun c =>
    (gamma16PrimeFibre N δ c).filter (fun p => Sifted N (N - gamma16Cofactor c * p) Z)
  let f (a : Gamma16OutputLabel) : Σ _ : Gamma16Profile, ℕ :=
    ⟨gamma16SwitchProfile N d a.1 a.2, a.1 3⟩
  have hmap : ∀ a ∈ S, f a ∈ T := by
    intro a ha
    obtain ⟨ha, hgd, hgN, hZ⟩ := mem_filter.mp ha
    obtain ⟨hp, hell⟩ := mem_sigma.mp ha
    have hs := gamma16_switch_profile_mem hN he hd hdW hp hell hgd hgN
    have hlt := gamma16_output_lt hN he (mem_sigma.mpr ⟨hp, hell⟩)
    have hq := gamma16_quotient_equation hlt (mem_filter.mp hell).2.2.1
    have hpos : 0 < gamma16Cofactor (gamma16SwitchProfile N d a.1 a.2) :=
      Nat.pos_of_mul_pos_right (hq.2.1 ▸ Nat.sub_pos_of_lt hlt)
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨hs.1, rfl⟩, mem_filter.mpr
      ⟨gamma16_strict_fibre_subset hpos hs.2, ?_⟩⟩
    rw [← hq.2.2.1]
    exact sifted_prime_of_le (mem_filter.mp hell).2.1 hZ
  have hinj : Set.InjOn f S := by
    intro a ha b hb hh
    have hp0 : a.1 0 = b.1 0 := congrArg (fun x : Σ _ : Gamma16Profile, ℕ => x.1.2.2.2.1) hh
    have hp1 : a.1 1 = b.1 1 := congrArg (fun x : Σ _ : Gamma16Profile, ℕ => x.1.2.2.1) hh
    have hp2 : a.1 2 = b.1 2 := congrArg (fun x : Σ _ : Gamma16Profile, ℕ => x.1.2.1) hh
    have hp3 : a.1 3 = b.1 3 := congrArg Sigma.snd hh
    have hp : a.1 = b.1 := by
      funext j
      fin_cases j
      · exact hp0
      · exact hp1
      · exact hp2
      · exact hp3
    have ha' := (mem_filter.mp ha).1
    have hb' := (mem_filter.mp hb).1
    have hqa := gamma16_quotient_equation (gamma16_output_lt hN he ha')
      (mem_filter.mp (mem_sigma.mp ha').2).2.2.1
    have hqb := gamma16_quotient_equation (gamma16_output_lt hN he hb')
      (mem_filter.mp (mem_sigma.mp hb').2).2.2.1
    have hout := congrArg (fun x : Σ _ : Gamma16Profile, ℕ =>
      N - gamma16Cofactor x.1 * x.2) hh
    exact gamma16_output_label_injective (Prod.ext
      (hqa.2.2.1.trans (hout.trans hqb.2.2.1.symm)) hp)
  have hc := card_le_card_of_injOn f hmap hinj
  have hcR : (S.card : ℝ) ≤ T.card := by exact_mod_cast hc
  simpa only [S, T, card_sigma, Nat.cast_sum] using hcR

theorem gamma16_prefix_finite_switching {i N : ℕ} {δ : ℝ} {W : Fin i → Finset ℕ}
    (hN : 4 ≤ N) (he : Even N) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    gamma16PrefixSum N δ W ≤
      gamma16S N δ (sqrt ((N : ℝ) ^ (1 / 2 - δ))) W +
        gamma16BadCount N δ W + gamma16ExceptionalCount N δ W := by
  let Z := sqrt ((N : ℝ) ^ (1 / 2 - δ))
  have hper (d : ℕ) (hdW : d ∈ boxConvolutionSupport W) :
      ((gamma16OutputLabels N δ d).card : ℝ) ≤
        (∑ c ∈ (gamma16Profiles N δ W).filter (fun c => c.1 = d),
          (((gamma16PrimeFibre N δ c).filter
            (fun p => Sifted N (N - gamma16Cofactor c * p) Z)).card : ℝ)) +
        (((gamma16OutputLabels N δ d).filter (fun a => Omega3BadD N d a.2)).card : ℝ) +
        (((gamma16OutputLabels N δ d).filter
          (fun a => a.2 ∈ omega3ExceptionalOutputs N δ)).card : ℝ) := by
    let S := gamma16OutputLabels N δ d
    let G := S.filter (fun a => ¬Omega3BadD N d a.2 ∧ ¬a.2 ∣ N ∧ Z ≤ (a.2 : ℝ))
    let B := S.filter (fun a => Omega3BadD N d a.2)
    let E := S.filter (fun a => a.2 ∈ omega3ExceptionalOutputs N δ)
    have hcover : S ⊆ G ∪ B ∪ E := by
      intro a ha
      by_cases hb : Omega3BadD N d a.2
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨ha, hb⟩))
      by_cases he : a.2 ∈ omega3ExceptionalOutputs N δ
      · exact mem_union_right _ (mem_filter.mpr ⟨ha, he⟩)
      have hprime := (mem_filter.mp (mem_sigma.mp ha).2).2.1
      have hn : ¬a.2 ∣ N := fun h => he (mem_omega3ExceptionalOutputs (by omega) hprime (Or.inr h))
      have hz : Z ≤ (a.2 : ℝ) := by
        by_contra h
        exact he (mem_omega3ExceptionalOutputs (by omega) hprime (Or.inl (lt_of_not_ge h)))
      exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨ha, hb, hn, hz⟩))
    have hc : (S.card : ℝ) ≤ G.card + B.card + E.card := by
      exact_mod_cast (card_le_card hcover).trans
        ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    have hg := gamma16_good_labels_le (δ := δ) (Z := Z) hN he (hd d hdW) hdW
    exact hc.trans (by dsimp only [G, B, E, S] at *; linarith)
  have hs := sum_le_sum (s := boxConvolutionSupport W) (fun d hdW =>
    mul_le_mul_of_nonneg_left (hper d hdW) (Nat.cast_nonneg (convolutionCoeff W d) : (0 : ℝ) ≤ _))
  simp only [mul_add, sum_add_distrib] at hs
  have hf :
      (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ c ∈ (gamma16Profiles N δ W).filter (fun c => c.1 = d),
          (((gamma16PrimeFibre N δ c).filter
            (fun p => Sifted N (N - gamma16Cofactor c * p) Z)).card : ℝ)) =
      gamma16S N δ Z W := by
    simp_rw [mul_sum]
    have hweight :
        (∑ d ∈ boxConvolutionSupport W, ∑ c ∈ (gamma16Profiles N δ W).filter (fun c => c.1 = d),
          (convolutionCoeff W d : ℝ) *
            (((gamma16PrimeFibre N δ c).filter (fun p => Sifted N (N - gamma16Cofactor c * p) Z)).card : ℝ)) =
        ∑ d ∈ boxConvolutionSupport W, ∑ c ∈ (gamma16Profiles N δ W).filter (fun c => c.1 = d),
          (convolutionCoeff W c.1 : ℝ) *
            (((gamma16PrimeFibre N δ c).filter (fun p => Sifted N (N - gamma16Cofactor c * p) Z)).card : ℝ) := by
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro c hc
      rw [(mem_filter.mp hc).2]
    rw [hweight]
    exact sum_fiberwise_of_maps_to (fun c hc => by
      rcases c with ⟨d, p3, p2, p1, n⟩
      exact (mem_gamma16Profiles.mp hc).1) _
  rw [hf] at hs
  simpa only [gamma16PrefixSum, gamma16OutputLabels, card_sigma, Nat.cast_sum,
    gamma16PrefixCarrier, sourceSieveCount, Int.cast_natCast, gamma16BadCount,
    gamma16ExceptionalCount] using hs

end Wu2008DoubleSieve

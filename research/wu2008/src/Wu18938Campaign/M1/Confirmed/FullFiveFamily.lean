import Wu18938Campaign.M1.Confirmed.FullFiveMass
import MathlibNt.Wu2008DoubleSieve.MotherPairGainAssembly

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullFive

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical

theorem finite_profile_upper (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (F : Finset (Rectangle p))
    (hF : (F : Set (Rectangle p)).Pairwise (fun r s =>
      Disjoint (Set.Ico r.A r.B ×ˢ Set.Ico r.C r.D) (Set.Ico s.A s.B ×ˢ Set.Ico s.C s.D)))
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ H : Rectangle p → ℝ,
      (∀ r ∈ F, 0 ≤ H r ∧ H r ≤ 1) →
      (∀ r ∈ F, ∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 2) (Pair.childEta p η) δ N k Δ U →
        wuBoxPhi N δ (convolutionWuWindows N Δ U) r.sample ≤
          (1 - H r + ρ) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U)) →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 5 ≤
        (Pair.classicalIntegral p .gammaFive -
          (∑ r ∈ F, H r * rectIntegral r.A r.B r.C r.D) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let C := Pair.classicalIntegral p .gammaFive
  have hC : 0 ≤ C := (MotherPair.classicalIntegral_bounds hp .gammaFive).1
  let ρ := min 1 (ε / (16 * (C + 1)))
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hpay : 16 * (C + 1) * ρ ≤ ε := by
    have hh := (le_div_iff₀ (show 0 < 16 * (C + 1) by positivity)).mp
      (min_le_right 1 (ε / (16 * (C + 1))))
    linarith only [hh]
  let ζ := ρ / ((F.card : ℝ) + 1)
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hζρ : (Fintype.card F : ℝ) * ζ ≤ ρ := by
    have heq : ((F.card : ℝ) + 1) * ζ = ρ := mul_div_cancel₀ _ (by positivity)
    rw [Fintype.card_coe]
    nlinarith only [heq,hζ.le]
  choose TP hTP4 hTP using (fun r : F => packing_node p hp r.val m hη hδ)
  choose TM hTM4 hTM using (fun r : F => packing_mass_lower p hp r.val m hη hδ hζ)
  obtain ⟨TC,hTC4,hTC⟩ := Pair.term_mask_upper p hp m hη hδ hρ hρ
  obtain ⟨TT,_,hTT⟩ := Pair.term_mass p hp m hη hδ hρ
  obtain ⟨TG,_,hTG⟩ := Pair.gain_mesh m hη hδ (show (0 : ℝ) < 1 by norm_num)
  refine ⟨ρ,hρ,max TC (max TT (max TG (max (univ.sup TP) (univ.sup TM)))),
    hTC4.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb H hH hn
  have hNP (r : F) : TP r ≤ N := by
    have hh := le_sup (f := TP) (mem_univ r)
    omega
  have hNM (r : F) : TM r ≤ N := by
    have hh := le_sup (f := TM) (mem_univ r)
    omega
  obtain ⟨hΔ,hR,_⟩ := hTG N (by omega) i Δ V hb
  let W := convolutionWuWindows N Δ V
  let L := termLabels p .gammaFive N δ W
  let P := fun r : F => packing N δ Δ V r.val
  let J := fun r : F => rectIntegral r.val.A r.val.B r.val.C r.val.D
  let Θ := boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W
  let M := gamma5ClassicalMainMass N δ W L
  let G := ∑ r : F, H r.val * J r
  have hrect (r : F) := hTP r N (hNP r) i Δ V hb (1 - H r.val + ρ)
    (hn r.val r.property)
  have hs : ∀ r : F, P r ⊆ L := fun r => (hrect r).1
  have hd : Pairwise (fun r s : F => Disjoint (P r) (P s)) := by
    intro r s hrs
    apply packing_disjoint hR hΔ
    exact hF r.property s.property (fun heq => hrs (Subtype.ext heq))
  have hθ : 0 ≤ Θ := Rebox.theta_nonneg hb (by omega) hη hδ
  have hclass := hTC N (by omega) heven i Δ V hb .gammaFive (L \ univ.biUnion P) sdiff_subset
  have hm0 (r : F) : 0 ≤ gamma5ClassicalMainMass N δ W (P r) := by
    have hh := Pair.term_mass_mono hb (by omega) hη hδ p hp .gammaFive (empty_subset (P r)) (hs r)
    simpa only [gamma5ClassicalMainMass,sum_empty,mul_zero] using hh
  have hupper := gamma5Gain_finite_upper hρ.le
    (term_count_partition p .gammaFive N δ W L P hd hs)
    (gamma5Gain_main_mass_partition N δ W L P hd hs) hm0 hclass
    (fun r => (hrect r).2)
  have hgain : (G - 2 * ρ) * Θ ≤
      ∑ r : F, H r.val * gamma5ClassicalMainMass N δ W (P r) := by
    apply gamma5Gain_weighted_transport (H := fun r : F => H r.val) (J := J)
      (m := fun r => gamma5ClassicalMainMass N δ W (P r))
      hθ hζ.le (fun r => hH r.val r.property)
      (fun r => hTM r N (hNM r) i Δ V hb) hζρ
    exact sub_le_self _ hρ.le
  have htotal := hTT N (by omega) i Δ V hb .gammaFive
  have hmass : M ≤ (C + ρ) * Θ := by
    have hh := (le_abs_self _).trans htotal
    change M - C * Θ ≤ ρ * Θ at hh
    linarith only [hh]
  have hmass' := mul_le_mul_of_nonneg_left hmass (sq_nonneg (1 + ρ))
  have hbudget := mul_le_mul_of_nonneg_right
    (gamma5Gain_budget (G := G) hC hρ.le hρ1 hpay) hθ
  have hG : G = ∑ r ∈ F, H r * rectIntegral r.A r.B r.C r.D :=
    Finset.sum_coe_sort F (fun r => H r * rectIntegral r.A r.B r.C r.D)
  have hdict := Pair.gamma_dictionary hb (by omega) hη hδ p hp .gammaFive
  simp only [Term.index] at hdict
  rw [← hdict,← hG]
  change termCount p .gammaFive N δ W L ≤ (C - G + ε) * Θ
  change termCount p .gammaFive N δ W L ≤ (1 + ρ) ^ 2 * M -
    (∑ r : F, H r.val * gamma5ClassicalMainMass N δ W (P r)) + ρ * Θ at hupper
  nlinarith only [hupper,hgain,hmass',hbudget]

end Wu18938Campaign.M1.Confirmed.FullFive

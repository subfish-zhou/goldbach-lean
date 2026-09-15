import Wu18938Campaign.M1.Confirmed.PairSource
import Wu18938Campaign.M1.Confirmed.ClassicalLeaves
import MathlibNt.Wu2008DoubleSieve.MotherPairGainComparison

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Pair

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical

theorem child_support {i N d : ℕ} {Δ P Q : ℝ} {V : Fin i → ℝ}
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ (Fin.cons P (Fin.cons Q V)))) :
    ∃ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
      gamma5ClassicalProduct x = d := by
  rw [convolutionWuWindows_cons,convolutionWuWindows_cons] at hd
  obtain ⟨v,hv,hvd⟩ := mem_image.mp hd
  have hv' := Fintype.mem_piFinset.mp hv
  let w : Fin i → ℕ := fun j => v j.succ.succ
  have hw : w ∈ Fintype.piFinset (convolutionWuWindows N Δ V) :=
    Fintype.mem_piFinset.mpr (fun j => hv' j.succ.succ)
  refine ⟨(∏ j, w j,v 0,v 1),mem_product.mpr
    ⟨mem_image.mpr ⟨w,hw,rfl⟩,mem_product.mpr ⟨hv' 0,hv' 1⟩⟩,?_⟩
  rw [← hvd,Fin.prod_univ_succ,Fin.prod_univ_succ]
  dsimp [gamma5ClassicalProduct,w]
  ring

theorem child_sum {i N : ℕ} (Δ P Q : ℝ) (V : Fin i → ℝ) (F : ℕ → ℝ) :
    (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ (Fin.cons P (Fin.cons Q V))),
      (convolutionCoeff (convolutionWuWindows N Δ (Fin.cons P (Fin.cons Q V))) d : ℝ) * F d) =
      ∑ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) * F (gamma5ClassicalProduct x) := by
  simp only [convolutionWuWindows_cons]
  exact gamma5Gain_double_sum _ _ _ _

theorem child_theta {i N : ℕ} (δ Δ P Q : ℝ) (V : Fin i → ℝ) :
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ (Fin.cons P (Fin.cons Q V))) =
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) :=
  gamma5Gain_cell_theta (child_sum Δ P Q V)

theorem child_rough {m i N : ℕ} {η δ Δ S U P Q : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hc : CapAdmissible S U)
    (hP : (N : ℝ) ^ (η * min (1 / S) ((1 - 2 * U) / 2)) ≤ P / Δ)
    (hQ : (N : ℝ) ^ (η * min (1 / S) ((1 - 2 * U) / 2)) ≤ Q / Δ)
    (hPN : P ≤ N) (hQN : Q ≤ N)
    (hsub : gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
      capLabels S U N δ (convolutionWuWindows N Δ V)) :
    RoughBox (m + 2) (η * min (1 / S) ((1 - 2 * U) / 2)) δ N (i + 2) Δ
      (Fin.cons P (Fin.cons Q V)) := by
  have hζ : η * min (1 / S) ((1 - 2 * U) / 2) ≤ η := by
    have hS : 0 < S := by linarith [hc.three_le_S]
    have hh : min (1 / S) ((1 - 2 * U) / 2) ≤ 1 :=
      (min_le_left _ _).trans ((div_le_iff₀ hS).mpr (by linarith [hc.three_le_S]))
    nlinarith
  have hpowers : (N : ℝ) ^ (η * min (1 / S) ((1 - 2 * U) / 2)) ≤ (N : ℝ) ^ η :=
    rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hζ
  refine ⟨by have := hb.depth; omega,hb.ratio_lower,hb.ratio_upper,?_,?_,?_,?_⟩
  · exact Fin.cases hP (Fin.cases hQ (fun j => hpowers.trans (hb.lower j)))
  · exact Fin.cases hPN (Fin.cases hQN hb.upper)
  · intro d hd
    obtain ⟨x,hx,rfl⟩ := child_support hd
    have hxd := (mem_product.mp hx).1
    have hxp := (mem_primeWindow.mp (mem_product.mp (mem_product.mp hx).2).1).1
    have hxq := (mem_primeWindow.mp (mem_product.mp (mem_product.mp hx).2).2).1
    have hmul : x.1 ≤ gamma5ClassicalProduct x := by
      dsimp [gamma5ClassicalProduct]
      exact (Nat.le_mul_of_pos_right _ hxp.pos).trans (Nat.le_mul_of_pos_right _ hxq.pos)
    exact (hb.support_large _ hxd).trans (by exact_mod_cast hmul)
  · intro d hd
    obtain ⟨x,hx,rfl⟩ := child_support hd
    have hg := geometry hb hN hη hδ hc (hsub hx)
    exact hg.cutoff_lower.trans hg.cutoff_le_level

theorem cell_count {m i N : ℕ} {η δ Δ P Q s : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : AnalyticParameters p) (j : Term) (hs : 0 < s)
    (hsub : gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
      termLabels p j N δ (convolutionWuWindows N Δ V))
    (hv : ∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
      Hratio p j (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ s) :
    termCount p j N δ (convolutionWuWindows N Δ V)
      (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ (Fin.cons P (Fin.cons Q V))) s := by
  rw [termCount_eq_sum]
  change _ ≤ ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ (Fin.cons P (Fin.cons Q V))),
    (convolutionCoeff (convolutionWuWindows N Δ (Fin.cons P (Fin.cons Q V))) d : ℝ) *
      (sourceSieveCount N d (d * N) (wuLocalCutoff N δ d s) : ℝ)
  rw [child_sum Δ]
  apply sum_le_sum
  intro x hx
  have hxl := hsub hx
  rw [termLabels_eq_rect] at hxl
  obtain ⟨hxa,hxp,hxq,_,_,_,_,_,_,hpq⟩ := mem_filter.mp hxl
  have hR := (hb.support_geometry hN hη hδ (mem_product.mp hxa).1).2.2.1
  have hz := term_cutoff_le_selected p j N δ _ (hsub hx)
  have hcut := term_cutoff_comparison p hp j hR hxp hxq hs (hv x hx)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  change (sourceSieveCount N (x.1 * x.2.1 * x.2.2) (x.1 * N) _ : ℝ) ≤ _
  rw [gamma5Classical_source_count_eq hxp hxq hz (hz.trans (by exact_mod_cast hpq.le))]
  exact gamma5Classical_source_count_antitone _ _ _ hcut

theorem cell_classical (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ P Q : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      (N : ℝ) ^ (η * min (1 / p.S) ((1 - 2 / p.kappa3) / 2)) ≤ P / Δ →
      (N : ℝ) ^ (η * min (1 / p.S) ((1 - 2 / p.kappa3) / 2)) ≤ Q / Δ →
      P ≤ N → Q ≤ N → ∀ (j : Term) (s : ℝ), 1 ≤ s → s ≤ 3 →
      gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
        termLabels p j N δ (convolutionWuWindows N Δ V) →
      (∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        Hratio p j (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ s) →
      termCount p j N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) ≤
        (1 + ε) * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) := by
  have hc := classical_cap hp
  have hζ : 0 < η * min (1 / p.S) ((1 - 2 * (1 / p.kappa3)) / 2) :=
    mul_pos hη (lt_min (by have := hc.three_le_S; positivity)
      (by linarith [hc.cap_lt_half]))
  obtain ⟨T,hT4,hT⟩ := roughBox_upper_leaf (m + 2) hζ hδ he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ P Q V hb hP hQ hPN hQN j s hs hs3 hsub hv
  have hsub' := hsub.trans (term_cap hb (by omega) hη hδ p hp j)
  have hchild := child_rough hb (by omega) hη hδ hc
    (by simpa only [mul_one_div] using hP) (by simpa only [mul_one_div] using hQ) hPN hQN hsub'
  have hbound := hT N hN heven (i + 2) Δ (Fin.cons P (Fin.cons Q V)) hchild s hs hs3
  rw [child_theta] at hbound
  exact (cell_count hb (by omega) hη hδ p hp j (by linarith) hsub hv).trans hbound

end Wu18938Campaign.M1.Confirmed.Pair

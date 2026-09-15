import Wu18938Campaign.M1.Confirmed.ClassicalInputs
import MathlibNt.Wu2008DoubleSieve.Omega3R1Source

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Omega

open Wu2008DoubleSieve Finset Real
open scoped Classical

theorem profile {m i N : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) {c : Omega3CofactorIndex}
    (hc : c ∈ omega3CofactorLabels N δ s t (convolutionWuWindows N Δ V)) :
    0 < omega3CofactorValue c ∧ omega3CofactorValue c ≤ N ∧
    (N : ℝ) ^ (η / 10) ≤ omega3CofactorValue c ∧
    (omega3CofactorValue c : ℝ) ≤ (N : ℝ) ^ (1 - η / 10) ∧
    (c.2.1 : ℝ) ≤ min ((N : ℝ) / omega3CofactorValue c) (wuLocalCutoff N δ c.1 s) ∧
    (omega3CofactorValue c : ℝ) *
      min ((N : ℝ) / omega3CofactorValue c) (wuLocalCutoff N δ c.1 s) ≤ N := by
  rcases c with ⟨d,p2,p1,n⟩
  obtain ⟨hd,h2,h1,_,hn,hsize,_⟩ := mem_omega3CofactorLabels.mp hc
  have hd0 := hb.support_pos hd
  have hp1 := (mem_primeWindow.mp h1).1.pos
  have hp2 := (mem_primeWindow.mp h2).1.pos
  have hepos : 0 < omega3CofactorValue ⟨d,p2,p1,n⟩ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd0 hn) hp1) hp2
  have her : (0 : ℝ) < omega3CofactorValue ⟨d,p2,p1,n⟩ := by exact_mod_cast hepos
  have hl : (N : ℝ) ^ (η / 10) ≤ p2 :=
    (roughBox_cutoff_lower hb hN hη hδ hd (by linarith) ht).trans
      (mem_primeWindow.mp h2).2.2.1
  have hpe : p2 ≤ omega3CofactorValue ⟨d,p2,p1,n⟩ :=
    Nat.le_mul_of_pos_left p2 (Nat.mul_pos (Nat.mul_pos hd0 hn) hp1)
  have heN : omega3CofactorValue ⟨d,p2,p1,n⟩ ≤ N :=
    (Nat.le_mul_of_pos_right _ hp2).trans hsize
  have hsizeR : (omega3CofactorValue ⟨d,p2,p1,n⟩ : ℝ) * p2 ≤ N := by exact_mod_cast hsize
  refine ⟨hepos,heN,hl.trans (by exact_mod_cast hpe),
    omega3_cofactor_power_gap (by omega) hl hsize,?_,?_⟩
  · exact le_min ((le_div_iff₀ her).mpr (by simpa only [mul_comm] using hsizeR))
      (mem_primeWindow.mp h2).2.2.2.le
  · have hu := (le_div_iff₀ her).mp
      (min_le_left ((N : ℝ) / omega3CofactorValue ⟨d,p2,p1,n⟩) (wuLocalCutoff N δ d s))
    simpa only [mul_comm] using hu

theorem cofactor_rough {m i N : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) {c : Omega3CofactorIndex}
    (hc : c ∈ omega3CofactorLabels N δ s t (convolutionWuWindows N Δ V)) :
    ∀ r, r.Prime → r ∣ omega3CofactorValue c → (N : ℝ) ^ (η / 10) ≤ r := by
  rcases c with ⟨d,p2,p1,n⟩
  obtain ⟨hd,h2,h1,_,_,_,hg⟩ := mem_omega3CofactorLabels.mp hc
  have hcut := roughBox_cutoff_lower hb hN hη hδ hd (by linarith : 1 ≤ t) ht
  have hw (j : Fin i) (q : ℕ) (hq : q ∈ convolutionWuWindows N Δ V j) :
      q.Prime ∧ (N : ℝ) ^ (η / 10) ≤ q :=
    ⟨(hb.window_large j q hq).1,
      (rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
        (by linarith : η / 10 ≤ η)).trans (hb.window_large j q hq).2⟩
  intro r hr hrd
  exact omega3_cofactor_prime_lower (mem_primeWindow.mp h1).1 (mem_primeWindow.mp h2).1
    (fun r hr hrd => omega3_support_prime_lower _ hw hd hr hrd)
    (hcut.trans (mem_primeWindow.mp h1).2.2.1) (hcut.trans (mem_primeWindow.mp h2).2.2.1) hg.2.2 hr hrd

theorem fibre {m i N : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) (e : ℕ) :
    (∑ c ∈ omega3LayerFibre (omega3CofactorLabels N δ s t (convolutionWuWindows N Δ V)) e,
      (convolutionCoeff (convolutionWuWindows N Δ V) c.1 : ℝ)) ≤
      (max 1 (1 / (η / 10))) ^ (m + 2) := by
  by_cases hne : (omega3LayerFibre
      (omega3CofactorLabels N δ s t (convolutionWuWindows N Δ V)) e).Nonempty
  · obtain ⟨c,hc⟩ := hne
    obtain ⟨hc,he⟩ := mem_filter.mp hc
    have hg := profile hb hN hη hδ hs hst ht hc
    apply omega3_cofactor_subcarrier_weight_le _ _ _ _
      (omega3_cofactor_labels_subset N δ s t _ e) hb.depth (by omega)
      (he ▸ hg.1) (he ▸ hg.2.1) (show 0 < η / 10 by positivity)
    · intro j q hq
      exact ⟨(hb.window_large j q hq).1,
        (rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
          (by linarith : η / 10 ≤ η)).trans (hb.window_large j q hq).2⟩
    · intro d hd
      exact roughBox_cutoff_lower hb hN hη hδ hd (by linarith) ht
  · rw [not_nonempty_iff_eq_empty.mp hne,sum_empty]
    positivity

theorem layers {m i N : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    let W := convolutionWuWindows N Δ V
    let L := omega3CofactorLabels N δ s t W
    let F := (max 1 (1 / (η / 10))) ^ (m + 2)
    (∀ e, (omega3LayerFibre L e).card ≤ ⌈F⌉₊) ∧
    (∀ j e, |omega3LayerCoefficient W L j e| ≤ F) := by
  intro W L F
  have hw := fibre hb hN hη hδ hs hst ht
  constructor
  · intro e
    exact_mod_cast (omega3_cofactor_fibre_card_le_weight N δ s t W e).trans
      ((hw e).trans (Nat.le_ceil F))
  · intro j e
    rw [abs_of_nonneg (omega3LayerCoefficient_nonneg W L j e)]
    exact omega3LayerCoefficient_le W L j e (by positivity) (hw e)

end Wu18938Campaign.M1.Confirmed.Omega

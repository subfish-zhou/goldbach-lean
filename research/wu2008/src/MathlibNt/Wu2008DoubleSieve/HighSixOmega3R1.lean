import MathlibNt.Wu2008DoubleSieve.HighSixOmega3Integral
import MathlibNt.Wu2008DoubleSieve.Omega3R1Source

namespace Wu2008DoubleSieve.HighSix.Omega3Upper
open Finset Real Filter
open scoped Classical Topology

/-- Geometry of the complete cofactor, including empty prime fibres. -/
theorem cofactor_profile_geometry {N : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) {c : Omega3CofactorIndex}
    (hc : c ∈ omega3CofactorLabels N δ s S (W N)) :
    0 < omega3CofactorValue c ∧ omega3CofactorValue c ≤ N ∧
    (N : ℝ)^(1/25 : ℝ) ≤ omega3CofactorValue c ∧
    (omega3CofactorValue c : ℝ) ≤ (N : ℝ)^(1-1/25 : ℝ) ∧
    (c.2.1 : ℝ) ≤ min ((N : ℝ)/omega3CofactorValue c) (wuLocalCutoff N δ c.1 s) ∧
    (omega3CofactorValue c : ℝ)*
      min ((N : ℝ)/omega3CofactorValue c) (wuLocalCutoff N δ c.1 s) ≤ N := by
  rcases c with ⟨d,p2,p1,n⟩
  obtain ⟨hd,h2,h1,_,hn,hsize,_⟩ := mem_omega3CofactorLabels.mp hc
  have hd0 := support_pos hd
  have hp1 := (mem_primeWindow.mp h1).1.pos
  have hp2 := (mem_primeWindow.mp h2).1.pos
  have hepos : 0 < omega3CofactorValue ⟨d,p2,p1,n⟩ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd0 hn) hp1) hp2
  have her : (0 : ℝ) < omega3CofactorValue ⟨d,p2,p1,n⟩ := by exact_mod_cast hepos
  have hl : (N : ℝ)^(1/25 : ℝ) ≤ p2 :=
    (inner_lower_cutoff hN hδ hδhi ((support N) ▸ hd)).trans
      (mem_primeWindow.mp h2).2.2.1
  have hpe : p2 ≤ omega3CofactorValue ⟨d,p2,p1,n⟩ :=
    Nat.le_mul_of_pos_left p2 (Nat.mul_pos (Nat.mul_pos hd0 hn) hp1)
  have heN : omega3CofactorValue ⟨d,p2,p1,n⟩ ≤ N :=
    (Nat.le_mul_of_pos_right _ hp2).trans hsize
  have hsizeR : (omega3CofactorValue ⟨d,p2,p1,n⟩ : ℝ)*p2 ≤ N := by exact_mod_cast hsize
  refine ⟨hepos,heN,hl.trans (by exact_mod_cast hpe),
    omega3_cofactor_power_gap (by omega) hl hsize,?_,?_⟩
  · exact le_min ((le_div_iff₀ her).mpr (by simpa only [mul_comm] using hsizeR))
      (mem_primeWindow.mp h2).2.2.2.le
  · have hu := (le_div_iff₀ her).mp
      (min_le_left ((N : ℝ)/omega3CofactorValue ⟨d,p2,p1,n⟩) (wuLocalCutoff N δ d s))
    simpa only [mul_comm] using hu

/-- A fixed copy bound from the actual prime coordinates and full cofactor. -/
theorem cofactor_fibre_weight {N : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (e : ℕ) :
    (∑ c ∈ omega3LayerFibre (omega3CofactorLabels N δ s S (W N)) e,
      (convolutionCoeff (W N) c.1 : ℝ)) ≤ (25 : ℝ)^3 := by
  by_cases hne : (omega3LayerFibre (omega3CofactorLabels N δ s S (W N)) e).Nonempty
  · obtain ⟨c,hc⟩ := hne
    obtain ⟨hc,he⟩ := mem_filter.mp hc
    have hg := cofactor_profile_geometry hN hδ hδhi hc
    have hb := omega3_cofactor_subcarrier_weight_le (k := 1) (η := 1/25)
      (W N) (fun d => wuLocalCutoff N δ d S) (fun d => wuLocalCutoff N δ d s)
      _ (omega3_cofactor_labels_subset N δ s S (W N) e) (by omega) (by omega)
      (he ▸ hg.1) (he ▸ hg.2.1) (by norm_num) (by
        intro j p hp
        change p ∈ P N at hp
        refine ⟨(mem_primeWindow.mp hp).1,?_⟩
        exact (rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ N by exact_mod_cast (by omega : 1 ≤ N))
          (by norm_num [left])).trans (mem_primeWindow.mp hp).2.2.1) (by
        intro d hd
        exact inner_lower_cutoff hN hδ hδhi ((support N) ▸ hd))
    norm_num [omega3LayerFibre] at hb ⊢
    exact hb
  · rw [not_nonempty_iff_eq_empty.mp hne,sum_empty]
    positivity

theorem cofactor_fibre_card {N : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (e : ℕ) :
    (omega3LayerFibre (omega3CofactorLabels N δ s S (W N)) e).card ≤ 25^3 := by
  exact_mod_cast (omega3_cofactor_fibre_card_le_weight N δ s S (W N) e).trans
    (cofactor_fibre_weight hN hδ hδhi e)

/-- Every occupied layer has coefficient one; the full copy count is separate. -/
theorem layer_coefficient_one {N j e : ℕ} {δ : ℝ}
    (he : e ∈ omega3LayerSupport (omega3CofactorLabels N δ s S (W N)) j) :
    omega3LayerCoefficient (W N) (omega3CofactorLabels N δ s S (W N)) j e = 1 := by
  rw [omega3LayerCoefficient_eq (W N) he]
  have hc := (omega3LayerLabel_mem he).1
  have hd := (mem_omega3CofactorLabels.mp hc).1
  rw [coeff ((support N) ▸ hd),Nat.cast_one]

/-- Actual high support consumes balanced BV with F=1, and all 25^3 copies. -/
theorem R1_log_saving {δ A : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Z : ℝ,
      omega3SieveR1 N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) δ s S Z (W N) ≤
        C*N/log (N : ℝ)^A := by
  obtain ⟨C,hC,T,hT4,hT⟩ := omega3_balanced_interval_distribution A (1/25) 1
    hA (by norm_num) (by norm_num) hδ
  refine ⟨(25 : ℝ)^3*C,by positivity,T,hT4,?_⟩
  intro N hN Z
  have hN2 : 2 ≤ N := by omega
  let L := omega3CofactorLabels N δ s S (W N)
  have hj (j : ℕ) :
      (∑ q ∈ omega3SieveModuli N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z,
        (3 : ℝ)^q.primeFactors.card *
          |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
            omega3LayerCoefficient (W N) L j e *
              omega3ProfileError N q e (omega3LayerLower L j e)
                (omega3LayerUpper N δ s L j e)|) ≤ C*N/log (N : ℝ)^A := by
    apply hT N hN (omega3LayerSupport L j) (omega3LayerCoefficient (W N) L j)
      (omega3LayerLower L j) (omega3LayerUpper N δ s L j)
    · intro e he
      have hc := omega3LayerLabel_mem he
      have hg := cofactor_profile_geometry hN2 hδ hδhi hc.1
      exact hc.2 ▸ ⟨hg.2.2.1,hg.2.2.2.1⟩
    · intro e he
      rw [layer_coefficient_one he,abs_one]
    · intro e he
      have hc := omega3LayerLabel_mem he
      have hg := cofactor_profile_geometry hN2 hδ hδhi hc.1
      refine ⟨omega3LayerLower_two he,?_,?_⟩
      · simpa only [omega3LayerLower,omega3LayerUpper,hc.2] using hg.2.2.2.2.1
      · simpa only [omega3LayerUpper,hc.2] using hg.2.2.2.2.2
  calc
    _ ≤ ∑ j ∈ range (25^3),
        ∑ q ∈ omega3SieveModuli N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z,
          (3 : ℝ)^q.primeFactors.card *
            |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
              omega3LayerCoefficient (W N) L j e *
                omega3ProfileError N q e (omega3LayerLower L j e)
                  (omega3LayerUpper N δ s L j e)| :=
      omega3SieveR1_le_layers (W N) (cofactor_fibre_card hN2 hδ hδhi)
        (fun _ hc => (cofactor_profile_geometry hN2 hδ hδhi hc).1)
    _ ≤ ∑ _j ∈ range (25^3), C*N/log (N : ℝ)^A := sum_le_sum (fun j _ => hj j)
    _ = _ := by simp; ring

end Wu2008DoubleSieve.HighSix.Omega3Upper

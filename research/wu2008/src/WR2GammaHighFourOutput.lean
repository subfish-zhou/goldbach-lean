import WR2GammaHighFourFibre

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve FourPrimeNonunit HighBoxRecovery Finset
open scoped Classical

theorem actual_fixed_output {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (k : Fin 4)
    (hW : ∀ r q, q ∈ windows j N r →
      q.Prime ∧ (N : ℝ)^(highEta) ≤ (q : ℝ)) (ell : ℕ) :
    (∑ x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k,
      (convolutionCoeff (windows j N) x.1 : ℝ) *
        ((actualFibre N δ (Wu04RemainingCore.row j) k x).filter (fun q => N-gamma16Cofactor x*q = ell)).card) ≤
      (max 1 (1/(highEta)))^5 := by
  let S := (actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k).sigma fun x =>
    (actualFibre N δ (Wu04RemainingCore.row j) k x).filter (fun q => N-gamma16Cofactor x*q = ell)
  let t (a : Σ _ : Gamma16Profile, ℕ) : Fin (3+1) → ℕ :=
    Fin.append (selected a.1) (fun _ : Fin 1 => a.2)
  have data (a : Σ _ : Gamma16Profile, ℕ) (ha : a ∈ S) :
      a.1 ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k ∧
      a.2.Prime ∧ (N : ℝ)^(highEta) ≤ (a.2 : ℝ) ∧
      gamma16Cofactor a.1*a.2 = N-ell := by
    obtain ⟨hx,hq,he⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    obtain ⟨_,hpr,ho,_,_,hcap,_⟩ := mem_filter.mp hq
    have gx := actual_profile_data j hN hδ hδhi k hx
    have hl : (N : ℝ)^(highEta) ≤ (a.1.2.1 : ℝ) := (gx.1 2).2
    refine ⟨hx,hpr,hl.trans (by exact_mod_cast ho.le), ?_⟩
    omega
  have heq : (∑ a ∈ S, (convolutionCoeff (windows j N) a.1.1 : ℝ)) =
      ∑ x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k,
      (convolutionCoeff (windows j N) x.1 : ℝ) *
        ((actualFibre N δ (Wu04RemainingCore.row j) k x).filter (fun q => N-gamma16Cofactor x*q = ell)).card := by
    simp only [S, sum_sigma, sum_const, nsmul_eq_mul, mul_comm]
  rw [← heq]
  by_cases hs : S.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have da := data a ha
    have ga := actual_profile_data j hN hδ hδhi k da.1
    have hepos : 0 < N-ell := da.2.2.2 ▸ Nat.mul_pos ga.2.2.1 da.2.1.pos
    apply HighNonunit.weighted_labels_le (windows j N) S (fun a => a.1.1) t
      (by norm_num : 1 ≤ 1) (by omega) hepos (Nat.sub_le N ell)
      (by norm_num [highEta] : 0 < highEta) hW
    · intro a ha
      rw [← (data a ha).2.2.2]
      exact ((((dvd_mul_right _ _).trans (dvd_mul_right _ _)).trans
        (dvd_mul_right _ _)).trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
    · intro a ha r
      have da := data a ha
      have ga := actual_profile_data j hN hδ hδhi k da.1
      refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · have hdv : selected a.1 r ∣ N-ell := by
          rw [← da.2.2.2]
          exact (selected_dvd a.1 r).trans (dvd_mul_right _ _)
        simpa only [t, Fin.append_left] using
          And.intro (ga.1 r).1 (And.intro hdv (ga.1 r).2)
      · have hdv : a.2 ∣ N-ell := by rw [← da.2.2.2]; exact dvd_mul_left _ _
        simpa only [t, Fin.append_right] using And.intro da.2.1 (And.intro hdv da.2.2.1)
    · intro a ha b hb' hd ht
      have da := data a ha
      have db := data b hb'
      have ga := actual_profile_data j hN hδ hδhi k da.1
      have hs : selected a.1 = selected b.1 := by
        funext r
        simpa only [t, Fin.append_left] using congr_fun ht (Fin.castAdd 1 r)
      have hq : a.2 = b.2 := by
        simpa only [t, Fin.append_right] using congr_fun ht (Fin.natAdd 3 0)
      have hc : gamma16Cofactor a.1 = gamma16Cofactor b.1 := by
        apply Nat.eq_of_mul_eq_mul_right da.2.1.pos
        exact da.2.2.2.trans (by simpa only [← hq] using db.2.2.2.symm)
      exact Sigma.ext (profile_recover hd hs ga.2.1 hc) (heq_of_eq hq)
  · rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.actual_fixed_output

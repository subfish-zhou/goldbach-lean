import WR2GammaHighTailSource
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveMultiplicity

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve HighNonunit HighBoxRecovery Finset
open scoped Classical

/-- Every actual primePrefix coordinate inherits the mother-window lower bound. -/
theorem actual_profile_data {N : ℕ} {δ : ℝ} (row : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (high : Bool) {x : Profile}
    (hx : x ∈ actualProfiles N δ (Wu04RemainingCore.row row) (windows row N) high) :
    x.1 ∈ boxConvolutionSupport (windows row N) ∧
    (primePrefix x).length = arity high ∧
    (∀ r ∈ primePrefix x, r.Prime ∧ (N : ℝ)^(highEta) ≤ (r : ℝ)) ∧
    0 < x.1 * (primePrefix x).prod ∧ 0 < cofactor x ∧ cofactor x ≤ N := by
  obtain ⟨hd,ht,hpn⟩ := mem_sigma.mp hx |>.imp_right mem_sigma.mp
  obtain ⟨hlen,_,hpre⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp ht
  obtain ⟨hpn,hn,_,_,_,hcap⟩ := mem_filter.mp hpn
  have hpen := (mem_product.mp hpn).1
  have hr : ∀ r ∈ primePrefix x, r.Prime ∧ (N : ℝ)^(highEta) ≤ (r : ℝ) := by
    intro r hr
    apply LowerTriple.window_lower row hN hδ hδhi hd
    rcases List.mem_append.mp hr with hr | hr
    · exact hpre r hr
    · have he : r = x.2.2.1 := by simpa using hr
      simpa [he] using hpen
  have hdpos := boxConvolutionSupport_pos (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) hd
  have hpp : 0 < (primePrefix x).prod := List.prod_pos (fun r hr' => (hr r hr').1.pos)
  have hco : 0 < cofactor x := by
    exact Nat.mul_pos (Nat.mul_pos hdpos (by omega)) hpp
  refine ⟨hd, ?_, hr, Nat.mul_pos hdpos hpp, hco, ?_⟩
  · cases high <;> simp_all [primePrefix, arity, word, HighUnitSource.word20, HighUnitSource.word21]
  · exact (Nat.le_mul_of_pos_right _ (mem_primeWindow.mp hpen).1.pos).trans hcap

/-- Fixed-cofactor full original sigma, with all ordered window and primePrefix labels. -/
theorem actual_fixed_cofactor {N : ℕ} {δ : ℝ} (row : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (high : Bool)
    (hW : ∀ j q, q ∈ windows row N j →
      q.Prime ∧ (N : ℝ)^(highEta) ≤ (q : ℝ)) (e : ℕ) :
    (∑ x ∈ (actualProfiles N δ (Wu04RemainingCore.row row) (windows row N) high).filter
      (fun x => cofactor x = e), (convolutionCoeff (windows row N) x.1 : ℝ)) ≤
      (max 1 (1/(highEta)))^(1+arity high) := by
  let S := (actualProfiles N δ (Wu04RemainingCore.row row) (windows row N) high).filter (fun x => cofactor x = e)
  by_cases hs : S.Nonempty
  · obtain ⟨x,hx⟩ := hs
    have hg := actual_profile_data row hN hδ hδhi high (mem_filter.mp hx).1
    have he := (mem_filter.mp hx).2
    apply weighted_labels_le _ S (fun x => x.1) (selected (arity high)) (by norm_num : 1 ≤ 1) (by omega)
      (he ▸ hg.2.2.2.2.1) (he ▸ hg.2.2.2.2.2)
      (by norm_num [highEta] : 0 < highEta) hW
    · intro a ha
      rw [← (mem_filter.mp ha).2]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · intro a ha j
      obtain ⟨ha,he⟩ := mem_filter.mp ha
      have hg := actual_profile_data row hN hδ hδhi high ha
      have hj : j.val < (primePrefix a).length := by rw [hg.2.1]; exact j.isLt
      have hm : selected (arity high) a j ∈ primePrefix a := by
        simp only [selected, List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hr := hg.2.2.1 _ hm
      refine ⟨hr.1, ?_, hr.2⟩
      rw [← he]
      exact (List.dvd_prod hm).trans (dvd_mul_left _ _)
    · intro a ha b hb' hd ht
      have ga := actual_profile_data row hN hδ hδhi high (mem_filter.mp ha).1
      have gb := actual_profile_data row hN hδ hδhi high (mem_filter.mp hb').1
      exact profile_recover ga.2.1 gb.2.1 hd ht ga.2.2.2.1
        ((mem_filter.mp ha).2.trans (mem_filter.mp hb').2.symm)
  · change (∑ x ∈ S, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

/-- Fixed output counts the final prime as well as every original sigma label. -/
theorem actual_fixed_output {N : ℕ} {δ : ℝ} (row : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (high : Bool)
    (hW : ∀ j q, q ∈ windows row N j →
      q.Prime ∧ (N : ℝ)^(highEta) ≤ (q : ℝ)) (ell : ℕ) :
    (∑ x ∈ actualProfiles N δ (Wu04RemainingCore.row row) (windows row N) high,
      (convolutionCoeff (windows row N) x.1 : ℝ) *
        ((actualFibre N δ (Wu04RemainingCore.row row) x).filter (fun q => N-cofactor x*q = ell)).card) ≤
      (max 1 (1/(highEta)))^(1+arity high+1) := by
  let S := (actualProfiles N δ (Wu04RemainingCore.row row) (windows row N) high).sigma fun x =>
    (actualFibre N δ (Wu04RemainingCore.row row) x).filter (fun q => N-cofactor x*q = ell)
  let t (a : Σ _ : Profile, ℕ) : Fin (arity high+1) → ℕ :=
    Fin.append (selected (arity high) a.1) (fun _ : Fin 1 => a.2)
  have data (a : Σ _ : Profile, ℕ) (ha : a ∈ S) :
      a.1 ∈ actualProfiles N δ (Wu04RemainingCore.row row) (windows row N) high ∧
      a.2.Prime ∧ (N : ℝ)^(highEta) ≤ (a.2 : ℝ) ∧
      cofactor a.1*a.2 = N-ell := by
    obtain ⟨hx,hq,he⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    obtain ⟨_,hpr,ho,_,_,hcap,_⟩ := mem_filter.mp hq
    have hg := actual_profile_data row hN hδ hδhi high hx
    have hl := (hg.2.2.1 a.1.2.2.1 (by simp [primePrefix])).2
    refine ⟨hx,hpr,hl.trans (by exact_mod_cast ho.le), ?_⟩
    omega
  have heq : (∑ a ∈ S, (convolutionCoeff (windows row N) a.1.1 : ℝ)) =
      ∑ x ∈ actualProfiles N δ (Wu04RemainingCore.row row) (windows row N) high,
      (convolutionCoeff (windows row N) x.1 : ℝ) *
        ((actualFibre N δ (Wu04RemainingCore.row row) x).filter (fun q => N-cofactor x*q = ell)).card := by
    simp only [S, sum_sigma, sum_const, nsmul_eq_mul, mul_comm]
  rw [← heq]
  by_cases hs : S.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have da := data a ha
    have ga := actual_profile_data row hN hδ hδhi high da.1
    have hepos : 0 < N-ell := da.2.2.2 ▸ Nat.mul_pos ga.2.2.2.2.1 da.2.1.pos
    have hbound := weighted_labels_le (windows row N) S (fun a => a.1.1) t
      (by norm_num : 1 ≤ 1) (by omega) hepos (Nat.sub_le N ell)
      (by norm_num [highEta] : 0 < highEta) hW
    have hresult : (∑ a ∈ S, (convolutionCoeff (windows row N) a.1.1 : ℝ)) ≤
        (max 1 (1/(highEta)))^(1+(arity high+1)) := by
      apply hbound
      · intro a ha
        rw [← (data a ha).2.2.2]
        exact (dvd_mul_of_dvd_left (dvd_mul_right _ _) _).trans (dvd_mul_right _ _)
      · intro a ha j
        have da := data a ha
        have ga := actual_profile_data row hN hδ hδhi high da.1
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · have hj : j.val < (primePrefix a.1).length := by rw [ga.2.1]; exact j.isLt
          have hm : selected (arity high) a.1 j ∈ primePrefix a.1 := by
            simp only [selected, List.getD_eq_getElem _ _ hj]
            exact List.getElem_mem hj
          have hr := ga.2.2.1 _ hm
          have hdv : selected (arity high) a.1 j ∣ N-ell := by
            rw [← da.2.2.2]
            exact ((List.dvd_prod hm).trans (dvd_mul_left _ _)).trans (dvd_mul_right _ _)
          simpa only [t, Fin.append_left] using And.intro hr.1 (And.intro hdv hr.2)
        · have hdv : a.2 ∣ N-ell := by rw [← da.2.2.2]; exact dvd_mul_left _ _
          simpa only [t, Fin.append_right] using And.intro da.2.1 (And.intro hdv da.2.2.1)
      · intro a ha b hb' hd ht
        have da := data a ha
        have db := data b hb'
        have ga := actual_profile_data row hN hδ hδhi high da.1
        have gb := actual_profile_data row hN hδ hδhi high db.1
        have hs : selected (arity high) a.1 = selected (arity high) b.1 := by
          funext j
          simpa only [t, Fin.append_left] using congr_fun ht (Fin.castAdd 1 j)
        have hq : a.2 = b.2 := by
          simpa only [t, Fin.append_right] using congr_fun ht (Fin.natAdd (arity high) 0)
        have hc : cofactor a.1 = cofactor b.1 := by
          apply Nat.eq_of_mul_eq_mul_right da.2.1.pos
          exact da.2.2.2.trans (by simpa only [← hq] using db.2.2.2.symm)
        exact Sigma.ext (profile_recover ga.2.1 gb.2.1 hd hs ga.2.2.2.1 hc) (heq_of_eq hq)
    simpa only [Nat.add_assoc] using hresult
  · rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.actual_fixed_cofactor
#print axioms WuPaper.R2GammaHigh.Tail.actual_fixed_output

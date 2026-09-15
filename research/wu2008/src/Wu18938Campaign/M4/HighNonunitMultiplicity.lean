import Wu18938Campaign.M4.HighWindowRough
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveMultiplicity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitActualFamily

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh WuSource.SrcSingle HighNonunit Finset Real
open scoped Classical

theorem original_window_large {N : ℕ} (j : Fin 3) (hN : 2 ≤ N) :
    ∀ k q, q ∈ windows j N k → q.Prime ∧ (N : ℝ) ^ (1 / 40 : ℝ) ≤ q := by
  intro k q hq
  have hm := mem_primeWindow.mp hq
  have hl := (seven_parameter_geometry (j.castAdd 4)).2.2.2.2.2.2.2.1
  exact ⟨hm.1, (rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega))
    (by linarith : (1 / 40 : ℝ) ≤ psiLeft (j.castAdd 4))).trans hm.2.2.1⟩

theorem original_nonunit_profile_data {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (high : Bool) {x : Profile}
    (hx : x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) high) :
    x.1 ∈ boxConvolutionSupport (windows j N) ∧
    (primePrefix x).length = arity high ∧
    (∀ q ∈ primePrefix x, q.Prime ∧ (N : ℝ) ^ (1 / 40 : ℝ) ≤ q) ∧
    0 < x.1 * (primePrefix x).prod ∧ 0 < cofactor x ∧ cofactor x ≤ N := by
  obtain ⟨hds, ht, hpn⟩ := mem_sigma.mp hx |>.imp_right mem_sigma.mp
  obtain ⟨hlen, _, hpre⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp ht
  obtain ⟨hpn, hn, _, _, _, hcap⟩ := mem_filter.mp hpn
  have hpen := (mem_product.mp hpn).1
  have hdm : x.1 ∈ psiPrimes (j.castAdd 4) N := by
    simpa only [support_eq] using hds
  have hr : ∀ q ∈ primePrefix x, q.Prime ∧ (N : ℝ) ^ (1 / 40 : ℝ) ≤ q := by
    intro q hq
    have hm : q ∈ primeWindow N
        (wuLocalCutoff N δ x.1 (Wu04RemainingCore.row j).S)
        (wuLocalCutoff N δ x.1 (Wu04RemainingCore.row j).s) := by
      rcases List.mem_append.mp hq with hq | hq
      · exact hpre q hq
      · have he : q = x.2.2.1 := by simpa using hq
        simpa only [he] using hpen
    exact ⟨(mem_primeWindow.mp hm).1, (original_label_bounds j hN hd hh hdm hm).2.1⟩
  have hdpos := (mem_primeWindow.mp hdm).1.pos
  have hpp : 0 < (primePrefix x).prod := List.prod_pos (fun q hq => (hr q hq).1.pos)
  have hco : 0 < cofactor x := Nat.mul_pos (Nat.mul_pos hdpos (by omega)) hpp
  refine ⟨hds, ?_, hr, Nat.mul_pos hdpos hpp, hco, ?_⟩
  · cases high <;> simp_all [primePrefix, arity, word, HighUnitSource.word20, HighUnitSource.word21]
  · exact (Nat.le_mul_of_pos_right _ (mem_primeWindow.mp hpen).1.pos).trans hcap

theorem original_nonunit_fixed_cofactor {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (high : Bool) (e : ℕ) :
    (∑ x ∈ (actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) high).filter
      (fun x => cofactor x = e), (convolutionCoeff (windows j N) x.1 : ℝ)) ≤
      (40 : ℝ) ^ (1 + arity high) := by
  let S := (actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) high).filter
    (fun x => cofactor x = e)
  by_cases hs : S.Nonempty
  · obtain ⟨x, hx⟩ := hs
    have hg := original_nonunit_profile_data j hN hd hh high (mem_filter.mp hx).1
    have he := (mem_filter.mp hx).2
    have hbound := weighted_labels_le (windows j N) S (fun x => x.1)
      (selected (arity high)) le_rfl (by omega : 1 < N)
      (he ▸ hg.2.2.2.2.1) (he ▸ hg.2.2.2.2.2)
      (by norm_num : (0 : ℝ) < 1 / 40) (original_window_large j hN)
    have hresult : (∑ x ∈ S, (convolutionCoeff (windows j N) x.1 : ℝ)) ≤
        (max 1 (1 / (1 / 40 : ℝ))) ^ (1 + arity high) := by
      apply hbound
      · intro a ha
        rw [← (mem_filter.mp ha).2]
        exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      · intro a ha k
        obtain ⟨ha, he⟩ := mem_filter.mp ha
        have hg := original_nonunit_profile_data j hN hd hh high ha
        have hk : k.val < (primePrefix a).length := by rw [hg.2.1]; exact k.isLt
        have hm : selected (arity high) a k ∈ primePrefix a := by
          simp only [selected, List.getD_eq_getElem _ _ hk]
          exact List.getElem_mem hk
        have hr := hg.2.2.1 _ hm
        refine ⟨hr.1, ?_, hr.2⟩
        rw [← he]
        exact (List.dvd_prod hm).trans (dvd_mul_left _ _)
      · intro a ha b hb hds ht
        have ga := original_nonunit_profile_data j hN hd hh high (mem_filter.mp ha).1
        have gb := original_nonunit_profile_data j hN hd hh high (mem_filter.mp hb).1
        exact profile_recover ga.2.1 gb.2.1 hds ht ga.2.2.2.1
          ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
    norm_num only [one_div_div, div_one, max_eq_right (by norm_num : (1 : ℝ) ≤ 40)] at hresult
    exact hresult
  · change (∑ x ∈ S, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

def originalNonunitFamily (j : Fin 3) (N : ℕ) (δ : ℝ) (high : Bool) :
    LabelledPhysical.Family Profile N :=
  actualFamily N δ (Wu04RemainingCore.row j) (windows j N) high
    (fun _ hd => (mem_primeWindow.mp (by simpa only [support_eq] using hd)).1.pos)

theorem original_nonunit_geometry {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (high : Bool) {x : Profile}
    (hx : x ∈ (originalNonunitFamily j N δ high).labels) :
    PhysicalGeometry N (1 / 40) (originalNonunitFamily j N δ high) x := by
  have hprof : x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) high :=
    (mem_filter.mp hx).1
  obtain ⟨hds, _, hm, _, _, hcap⟩ := profile_data hprof
  have hdm : x.1 ∈ psiPrimes (j.castAdd 4) N := by
    simpa only [support_eq] using hds
  have hlarge := (original_label_bounds j hN hd hh hdm hm).2.1
  have hg := (originalNonunitFamily j N δ high).geometry x hx
  have hpos : 0 < cofactor x := hg.1
  have hle : cofactor x ≤ N :=
    (Nat.le_mul_of_pos_right _ (mem_primeWindow.mp hm).1.pos).trans hcap
  have hpow : (N : ℝ) ^ (1 / 40 : ℝ) ≤ cofactor x :=
    hlarge.trans (by exact_mod_cast Nat.le_of_dvd hpos (penultimate_dvd x))
  exact ⟨hpos, hle, hpow, omega3_cofactor_power_gap (by omega) hlarge hcap,
    hg.2.1, hlarge.trans (le_max_left _ _), hg.2.2.1, hg.2.2.2⟩

theorem original_nonunit_relative {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (high : Bool) {x : Profile}
    (hx : x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) high) :
    ∀ q, q.Prime → q ∣ cofactor x → q.Coprime N → (N : ℝ) ^ (1 / 40 : ℝ) ≤ q := by
  obtain ⟨hds, hpre, hm, _, hs, _⟩ := profile_data hx
  have hdm : x.1 ∈ psiPrimes (j.castAdd 4) N := by
    simpa only [support_eq] using hds
  have hpen := (original_label_bounds j hN hd hh hdm hm).2.1
  have hprefix := RelativeRoughness.masked_prefix x.2.1 hs hpen
    (fun q hq hqd => omega3_support_prime_lower _ (original_window_large j hN) hds hq hqd)
    (fun r hr => ⟨(mem_primeWindow.mp (hpre r hr)).1,
      (original_label_bounds j hN hd hh hdm (hpre r hr)).2.1⟩)
  have hlast : ∀ q : ℕ, q.Prime → q ∣ x.2.2.1 → q.Coprime N →
      (N : ℝ) ^ (1 / 40 : ℝ) ≤ q := by
    intro q hq hqd _
    have heq : q = x.2.2.1 :=
      ((Nat.dvd_prime (mem_primeWindow.mp hm).1).mp hqd).resolve_left hq.ne_one
    simpa only [heq] using hpen
  have hfull := RelativeRoughness.mul hprefix hlast
  simpa only [cofactor, List.prod_append, List.prod_singleton, mul_assoc, mul_left_comm,
    mul_comm] using hfull

end Wu18938Campaign.M4

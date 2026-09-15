import Wu18938Campaign.M1.Confirmed.HighNonunit

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighNonunit Finset Real
open scoped Classical

theorem roughBox_weightAt {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (high : Bool) (ell : ℕ) :
    (sourceFamily N δ Δ V p high).weightAt ell ≤
      (max 1 (1 / (η / 10))) ^ (m + 6) := by
  let L := sourceFamily N δ Δ V p high
  let S := L.labels.sigma fun x => (L.primes x).filter
    (fun q => N - L.cofactor x * q = ell)
  let t (a : Σ _ : Profile, ℕ) : Fin (arity high + 1) → ℕ :=
    Fin.append (selected (arity high) a.1) (fun _ : Fin 1 => a.2)
  have data (a : Σ _ : Profile, ℕ) (ha : a ∈ S) :
      a.1 ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high ∧
      a.2.Prime ∧ (N : ℝ) ^ (η / 10) ≤ (a.2 : ℝ) ∧
      cofactor a.1 * a.2 = N - ell := by
    obtain ⟨hx, hq, he⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    have hg := roughBox_physical_geometry hb hN hη hδ p hp high hx
    have hprod := L.output_le hx hq
    refine ⟨(mem_filter.mp hx).1, (mem_filter.mp hq).2.1,
      hg.lower_large.trans (mem_filter.mp hq).2.2.1.le, ?_⟩
    change cofactor a.1 * a.2 ≤ N at hprod
    change N - cofactor a.1 * a.2 = ell at he
    omega
  have heq : L.weightAt ell =
      ∑ a ∈ S, (convolutionCoeff (convolutionWuWindows N Δ V) a.1.1 : ℝ) := by
    simp only [LabelledPhysical.Family.weightAt, S, sum_sigma, sum_const, nsmul_eq_mul]
    apply sum_congr rfl
    intro x _
    exact mul_comm _ _
  rw [heq]
  by_cases hs : S.Nonempty
  · obtain ⟨a, ha⟩ := hs
    have da := data a ha
    have ga := roughBox_profile_data hb hN hη hδ p hp high da.1
    have hepos : 0 < N - ell := da.2.2.2 ▸ Nat.mul_pos ga.2.2.2.2.1 da.2.1.pos
    have hbound := weighted_labels_le (convolutionWuWindows N Δ V) S
      (fun a => a.1.1) t hb.depth (by omega) hepos (Nat.sub_le N ell)
      (show 0 < η / 10 by positivity) (roughBox_window_tenth hb hN hη)
    have hresult :
        (∑ a ∈ S, (convolutionCoeff (convolutionWuWindows N Δ V) a.1.1 : ℝ)) ≤
          (max 1 (1 / (η / 10))) ^ (m + (arity high + 1)) := by
      apply hbound
      · intro a ha
        rw [← (data a ha).2.2.2]
        exact (dvd_mul_of_dvd_left (dvd_mul_right _ _) _).trans (dvd_mul_right _ _)
      · intro a ha j
        have da := data a ha
        have ga := roughBox_profile_data hb hN hη hδ p hp high da.1
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · have hj : j.val < (primePrefix a.1).length := by rw [ga.2.1]; exact j.isLt
          have hm : selected (arity high) a.1 j ∈ primePrefix a.1 := by
            simp only [selected, List.getD_eq_getElem _ _ hj]
            exact List.getElem_mem hj
          have hr := ga.2.2.1 _ hm
          have hdv : selected (arity high) a.1 j ∣ N - ell := by
            rw [← da.2.2.2]
            exact ((List.dvd_prod hm).trans (dvd_mul_left _ _)).trans (dvd_mul_right _ _)
          simpa only [t, Fin.append_left] using And.intro hr.1 (And.intro hdv hr.2)
        · have hdv : a.2 ∣ N - ell := by
            rw [← da.2.2.2]
            exact dvd_mul_left _ _
          simpa only [t, Fin.append_right] using And.intro da.2.1 (And.intro hdv da.2.2.1)
      · intro a ha b hb' hd ht
        have da := data a ha
        have db := data b hb'
        have ga := roughBox_profile_data hb hN hη hδ p hp high da.1
        have gb := roughBox_profile_data hb hN hη hδ p hp high db.1
        have hs : selected (arity high) a.1 = selected (arity high) b.1 := by
          funext j
          simpa only [t, Fin.append_left] using congr_fun ht (Fin.castAdd 1 j)
        have hq : a.2 = b.2 := by
          simpa only [t, Fin.append_right] using congr_fun ht (Fin.natAdd (arity high) 0)
        have hc : cofactor a.1 = cofactor b.1 := by
          apply Nat.eq_of_mul_eq_mul_right da.2.1.pos
          exact da.2.2.2.trans (by simpa only [← hq] using db.2.2.2.symm)
        exact Sigma.ext (profile_recover ga.2.1 gb.2.1 hd hs ga.2.2.2.1 hc) (heq_of_eq hq)
    exact hresult.trans (pow_le_pow_right₀ (le_max_left _ _)
      (by cases high <;> simp [arity]))
  · rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

theorem roughBox_small_finite {m i N : ℕ} {η δ Δ Z : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (high : Bool)
    (hZ : 0 ≤ Z) :
    (sourceFamily N δ Δ V p high).small Z ≤
      (max 1 (1 / (η / 10))) ^ (m + 6) * (Z + 1) := by
  let L := sourceFamily N δ Δ V p high
  let S := (range (N + 1)).filter (fun (ell : ℕ) => ell.Prime ∧ (ell : ℝ) < Z)
  have he : L.small Z = ∑ ell ∈ S, L.weightAt ell := by
    have h := L.output_test (fun ell => if ell.Prime ∧ (ell : ℝ) < Z then 1 else 0)
    simpa only [LabelledPhysical.Family.small, S, sum_filter, card_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum,
      mul_ite, mul_one, mul_zero] using h.symm
  have hsub : S ⊆ range (⌊Z⌋₊ + 1) := by
    intro ell hell
    have hlt := (mem_filter.mp hell).2.2
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hZ).mpr hlt.le))
  calc
    _ = ∑ ell ∈ S, L.weightAt ell := he
    _ ≤ ∑ _ell ∈ S, (max 1 (1 / (η / 10))) ^ (m + 6) :=
      sum_le_sum (fun ell _ => roughBox_weightAt hb hN hη hδ p hp high ell)
    _ = (max 1 (1 / (η / 10))) ^ (m + 6) * (S.card : ℝ) := by simp [mul_comm]
    _ ≤ (max 1 (1 / (η / 10))) ^ (m + 6) * ((⌊Z⌋₊ + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left
        (by exact_mod_cast (show S.card ≤ ⌊Z⌋₊ + 1 by simpa using card_le_card hsub))
        (by positivity)
    _ ≤ _ := by
      push_cast
      exact mul_le_mul_of_nonneg_left (add_le_add (Nat.floor_le hZ) le_rfl) (by positivity)

end Wu18938Campaign.M1.Confirmed

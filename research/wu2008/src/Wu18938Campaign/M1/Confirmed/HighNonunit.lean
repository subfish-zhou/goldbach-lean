import Wu18938Campaign.M1.Confirmed.RoughBox
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveMultiplicity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitActualFamily
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledRelativeRoughness

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighNonunit Finset Real
open scoped Classical

theorem roughBox_window_tenth {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) :
    ∀ j q, q ∈ convolutionWuWindows N Δ V j →
      q.Prime ∧ (N : ℝ) ^ (η / 10) ≤ (q : ℝ) := by
  intro j q hq
  have hw := hb.window_large j q hq
  exact ⟨hw.1, (rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith : η / 10 ≤ η)).trans hw.2⟩

theorem roughBox_profile_data {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (high : Bool)
    {x : Profile} (hx : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high) :
    x.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ∧
    (primePrefix x).length = arity high ∧
    (∀ q ∈ primePrefix x, q.Prime ∧ (N : ℝ) ^ (η / 10) ≤ (q : ℝ)) ∧
    0 < x.1 * (primePrefix x).prod ∧ 0 < cofactor x ∧ cofactor x ≤ N := by
  obtain ⟨hd, ht, hpn⟩ := mem_sigma.mp hx |>.imp_right mem_sigma.mp
  obtain ⟨hlen, _, hpre⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp ht
  obtain ⟨hpn, hn, _, _, _, hcap⟩ := mem_filter.mp hpn
  have hpen := (mem_product.mp hpn).1
  have hr : ∀ q ∈ primePrefix x, q.Prime ∧ (N : ℝ) ^ (η / 10) ≤ (q : ℝ) := by
    intro q hq
    apply hb.mother_window_large hN hη hδ p hp hd
    rcases List.mem_append.mp hq with hq | hq
    · exact hpre q hq
    · have he : q = x.2.2.1 := by simpa using hq
      simpa only [he] using hpen
  have hdpos := hb.support_pos hd
  have hpp : 0 < (primePrefix x).prod := List.prod_pos (fun q hq => (hr q hq).1.pos)
  have hco : 0 < cofactor x := Nat.mul_pos (Nat.mul_pos hdpos (by omega)) hpp
  refine ⟨hd, ?_, hr, Nat.mul_pos hdpos hpp, hco, ?_⟩
  · cases high <;> simp_all [primePrefix, arity, word, HighUnitSource.word20, HighUnitSource.word21]
  · exact (Nat.le_mul_of_pos_right _ (mem_primeWindow.mp hpen).1.pos).trans hcap

theorem roughBox_fixed_cofactor {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (high : Bool) (e : ℕ) :
    (∑ x ∈ (actualProfiles N δ p (convolutionWuWindows N Δ V) high).filter
      (fun x => cofactor x = e), (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ)) ≤
      (max 1 (1 / (η / 10))) ^ (m + arity high) := by
  let S := (actualProfiles N δ p (convolutionWuWindows N Δ V) high).filter
    (fun x => cofactor x = e)
  by_cases hs : S.Nonempty
  · obtain ⟨x, hx⟩ := hs
    have hg := roughBox_profile_data hb hN hη hδ p hp high (mem_filter.mp hx).1
    have he := (mem_filter.mp hx).2
    apply weighted_labels_le _ S (fun x => x.1) (selected (arity high)) hb.depth
      (by omega) (he ▸ hg.2.2.2.2.1) (he ▸ hg.2.2.2.2.2)
      (by positivity : 0 < η / 10) (roughBox_window_tenth hb hN hη)
    · intro a ha
      rw [← (mem_filter.mp ha).2]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · intro a ha j
      obtain ⟨ha, he⟩ := mem_filter.mp ha
      have hg := roughBox_profile_data hb hN hη hδ p hp high ha
      have hj : j.val < (primePrefix a).length := by rw [hg.2.1]; exact j.isLt
      have hm : selected (arity high) a j ∈ primePrefix a := by
        simp only [selected, List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hr := hg.2.2.1 _ hm
      refine ⟨hr.1, ?_, hr.2⟩
      rw [← he]
      exact (List.dvd_prod hm).trans (dvd_mul_left _ _)
    · intro a ha b hb' hds ht
      have ga := roughBox_profile_data hb hN hη hδ p hp high (mem_filter.mp ha).1
      have gb := roughBox_profile_data hb hN hη hδ p hp high (mem_filter.mp hb').1
      exact profile_recover ga.2.1 gb.2.1 hds ht ga.2.2.2.1
        ((mem_filter.mp ha).2.trans (mem_filter.mp hb').2.symm)
  · change (∑ x ∈ S, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

theorem roughBox_physical_geometry {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (high : Bool)
    {x : Profile} (hx : x ∈ (sourceFamily N δ Δ V p high).labels) :
    PhysicalGeometry N (η / 10) (sourceFamily N δ Δ V p high) x := by
  have hprof : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high :=
    (mem_filter.mp hx).1
  obtain ⟨hd, _, hm, _, _, hcap⟩ := profile_data hprof
  have hlarge := hb.mother_window_large hN hη hδ p hp hd hm
  have hg := (sourceFamily N δ Δ V p high).geometry x hx
  have hpos : 0 < cofactor x := hg.1
  have hle : cofactor x ≤ N := (Nat.le_mul_of_pos_right _ hlarge.1.pos).trans hcap
  have hpow : (N : ℝ) ^ (η / 10) ≤ cofactor x :=
    hlarge.2.trans (by exact_mod_cast Nat.le_of_dvd hpos (penultimate_dvd x))
  exact ⟨hpos, hle, hpow, omega3_cofactor_power_gap (by omega) hlarge.2 hcap,
    hg.2.1, hlarge.2.trans (le_max_left _ _), hg.2.2.1, hg.2.2.2⟩

theorem roughBox_relative_roughness {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (high : Bool)
    {x : Profile} (hx : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high) :
    ∀ q, q.Prime → q ∣ cofactor x → q.Coprime N → (N : ℝ) ^ (η / 10) ≤ (q : ℝ) := by
  obtain ⟨hd, hpre, hm, _, hs, _⟩ := profile_data hx
  have hpen := hb.mother_window_large hN hη hδ p hp hd hm
  have hprefix := RelativeRoughness.masked_prefix x.2.1 hs hpen.2
    (fun q hq hqd => omega3_support_prime_lower _
      (roughBox_window_tenth hb hN hη) hd hq hqd)
    (fun r hr => hb.mother_window_large hN hη hδ p hp hd (hpre r hr))
  have hlast : ∀ q : ℕ, q.Prime → q ∣ x.2.2.1 → q.Coprime N →
      (N : ℝ) ^ (η / 10) ≤ (q : ℝ) := by
    intro q hq hqd _
    have heq : q = x.2.2.1 := ((Nat.dvd_prime hpen.1).mp hqd).resolve_left hq.ne_one
    simpa only [heq] using hpen.2
  have hfull := RelativeRoughness.mul hprefix hlast
  simpa only [cofactor, List.prod_append, List.prod_singleton, mul_assoc, mul_left_comm,
    mul_comm] using hfull

theorem roughBox_family_fibre {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (high : Bool) (e : ℕ) :
    let L := sourceFamily N δ Δ V p high
    (∑ x ∈ L.labels.filter (fun x => L.cofactor x = e), L.weight x) ≤
      (max 1 (1 / (η / 10))) ^ (m + 5) := by
  let L := sourceFamily N δ Δ V p high
  have hs : L.labels.filter (fun x => L.cofactor x = e) ⊆
      (actualProfiles N δ p (convolutionWuWindows N Δ V) high).filter
        (fun x => cofactor x = e) := by
    intro x hx
    obtain ⟨hx, he⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨(mem_filter.mp hx).1, he⟩
  calc
    _ ≤ ∑ x ∈ (actualProfiles N δ p (convolutionWuWindows N Δ V) high).filter
        (fun x => cofactor x = e), (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ (max 1 (1 / (η / 10))) ^ (m + arity high) :=
      roughBox_fixed_cofactor hb hN hη hδ p hp high e
    _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) (by cases high <;> simp [arity])

theorem roughBox_gamma_le_unit_family {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (he : Even N)
    (p : SecondFunctionalParameters) (high : Bool) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V)
        (if high then 21 else 20) ≤
      actualUnit N δ p (convolutionWuWindows N Δ V) high +
        (sourceFamily N δ Δ V p high).primeMass := by
  rw [← actual_partition]
  apply add_le_add le_rfl
  change actualSource N δ p (convolutionWuWindows N Δ V) high ≤
    (actualFamily N δ p (convolutionWuWindows N Δ V) high
      (fun _ hd => hb.support_pos hd)).primeMass
  rw [(actualFamily_dictionary N δ p (convolutionWuWindows N Δ V) high
    (fun _ hd => hb.support_pos hd)).1]
  exact source_le_envelope (fun _ hd => hb.support_pos hd) hN he
    (word_length high) (word_last high)

end Wu18938Campaign.M1.Confirmed

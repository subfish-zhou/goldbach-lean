import Wu18938Campaign.M1.Confirmed.LabelledDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeExceptionBounds

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Four

open Wu2008DoubleSieve FourPrimeNonunit Finset Real
open scoped Classical

theorem profile (m i N : ℕ) {η δ Δ : ℝ} (V : Fin i → ℝ)
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 4)
    {x : Gamma16Profile} (hx : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j) :
    (∀ r, (selected x r).Prime ∧ (N : ℝ) ^ (η / 10) ≤ (selected x r : ℝ)) ∧
    0 < x.1*x.2.2.2.1*x.2.2.1*x.2.1 ∧
    0 < gamma16Cofactor x ∧ gamma16Cofactor x ≤ N := by
  obtain ⟨hd,h3,h2,h1,_,hn,_,_,_,_,hcap⟩ := profile_data hx
  have g1 := hb.mother_window_large hN hη hδ p hp hd h1
  have g2 := hb.mother_window_large hN hη hδ p hp hd h2
  have g3 := hb.mother_window_large hN hη hδ p hp hd h3
  have hdpos := hb.support_pos hd
  refine ⟨?_, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdpos g1.1.pos) g2.1.pos) g3.1.pos,
    ?_, (Nat.le_mul_of_pos_right _ g3.1.pos).trans hcap⟩
  · intro r
    fin_cases r
    · exact g1
    · exact g2
    · exact g3
  · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdpos (by omega))
      g1.1.pos) g2.1.pos) g3.1.pos

theorem geometry {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 4)
    {x : Gamma16Profile} (hx : x ∈ (sourceFamily N δ Δ V p j).labels) :
    PhysicalGeometry N (η / 10) (sourceFamily N δ Δ V p j) x := by
  have hprof : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j :=
    (mem_filter.mp hx).1
  obtain ⟨hd,hm,_,_,_,_,_,_,_,_,hcap⟩ := profile_data hprof
  have hlarge := hb.mother_window_large hN hη hδ p hp hd hm
  have hg := (sourceFamily N δ Δ V p j).geometry x hx
  have hpos : 0 < gamma16Cofactor x := hg.1
  have hle : gamma16Cofactor x ≤ N := (Nat.le_mul_of_pos_right _ hlarge.1.pos).trans hcap
  have hpow : (N : ℝ) ^ (η / 10) ≤ gamma16Cofactor x :=
    hlarge.2.trans (by exact_mod_cast Nat.le_of_dvd hpos (penultimate_dvd x))
  exact ⟨hpos, hle, hpow, omega3_cofactor_power_gap (by omega) hlarge.2 hcap,
    hg.2.1, hlarge.2.trans (le_max_left _ _), hg.2.2.1, hg.2.2.2⟩

theorem fixed_cofactor {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 4) (e : ℕ) :
    (∑ x ∈ (actualProfiles N δ p (convolutionWuWindows N Δ V) j).filter
      (fun x => gamma16Cofactor x = e),
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ)) ≤
      (max 1 (1 / (η / 10))) ^ (m + 3) := by
  let S := (actualProfiles N δ p (convolutionWuWindows N Δ V) j).filter
    (fun x => gamma16Cofactor x = e)
  by_cases hs : S.Nonempty
  · obtain ⟨x,hx⟩ := hs
    have gx := profile m i N V hb hN hη hδ p hp j (mem_filter.mp hx).1
    have he := (mem_filter.mp hx).2
    apply HighNonunit.weighted_labels_le _ S (fun x => x.1) selected hb.depth (by omega)
      (he ▸ gx.2.2.1) (he ▸ gx.2.2.2) (by positivity : 0 < η / 10)
      (roughBox_window_tenth hb hN hη)
    · intro a ha
      rw [← (mem_filter.mp ha).2]
      exact (((dvd_mul_right _ _).trans (dvd_mul_right _ _)).trans
        (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
    · intro a ha r
      have ga := profile m i N V hb hN hη hδ p hp j (mem_filter.mp ha).1
      exact ⟨(ga.1 r).1, (mem_filter.mp ha).2 ▸ selected_dvd a r, (ga.1 r).2⟩
    · intro a ha b hb' hd ht
      have ga := profile m i N V hb hN hη hδ p hp j (mem_filter.mp ha).1
      exact profile_recover hd ht ga.2.1
        ((mem_filter.mp ha).2.trans (mem_filter.mp hb').2.symm)
  · change (∑ x ∈ S, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

theorem family_fibre {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 4) (e : ℕ) :
    let L := sourceFamily N δ Δ V p j
    (∑ x ∈ L.layerFibre e, L.weight x) ≤ (max 1 (1 / (η / 10))) ^ (m + 3) := by
  let L := sourceFamily N δ Δ V p j
  have hs : L.layerFibre e ⊆
      (actualProfiles N δ p (convolutionWuWindows N Δ V) j).filter
        (fun x => gamma16Cofactor x = e) := by
    intro x hx
    obtain ⟨hx, he⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨(mem_filter.mp hx).1, he⟩
  exact (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.cast_nonneg _)).trans
    (fixed_cofactor hb hN hη hδ p hp j e)

theorem fixed_output {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 4) (ell : ℕ) :
    (∑ x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j,
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
        ((actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)).card) ≤
      (max 1 (1 / (η / 10))) ^ (m + 4) := by
  let S := (actualProfiles N δ p (convolutionWuWindows N Δ V) j).sigma fun x =>
    (actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)
  let t (a : Σ _ : Gamma16Profile, ℕ) : Fin (3+1) → ℕ :=
    Fin.append (selected a.1) (fun _ : Fin 1 => a.2)
  have data (a : Σ _ : Gamma16Profile, ℕ) (ha : a ∈ S) :
      a.1 ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j ∧
      a.2.Prime ∧ (N : ℝ) ^ (η / 10) ≤ (a.2 : ℝ) ∧
      gamma16Cofactor a.1*a.2 = N-ell := by
    obtain ⟨hx,hq,he⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    obtain ⟨_,hpr,ho,_,_,hcap,_⟩ := mem_filter.mp hq
    have gx := profile m i N V hb hN hη hδ p hp j hx
    have hl : (N : ℝ) ^ (η / 10) ≤ (a.1.2.1 : ℝ) := (gx.1 2).2
    refine ⟨hx,hpr,hl.trans (by exact_mod_cast ho.le), ?_⟩
    omega
  have heq : (∑ a ∈ S, (convolutionCoeff (convolutionWuWindows N Δ V) a.1.1 : ℝ)) =
      ∑ x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j,
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
        ((actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)).card := by
    simp only [S, sum_sigma, sum_const, nsmul_eq_mul, mul_comm]
  rw [← heq]
  by_cases hs : S.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have da := data a ha
    have ga := profile m i N V hb hN hη hδ p hp j da.1
    have hepos : 0 < N-ell := da.2.2.2 ▸ Nat.mul_pos ga.2.2.1 da.2.1.pos
    apply HighNonunit.weighted_labels_le (convolutionWuWindows N Δ V) S (fun a => a.1.1) t
      hb.depth (by omega) hepos (Nat.sub_le N ell) (by positivity : 0 < η / 10)
      (roughBox_window_tenth hb hN hη)
    · intro a ha
      rw [← (data a ha).2.2.2]
      exact ((((dvd_mul_right _ _).trans (dvd_mul_right _ _)).trans
        (dvd_mul_right _ _)).trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
    · intro a ha r
      have da := data a ha
      have ga := profile m i N V hb hN hη hδ p hp j da.1
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
      have ga := profile m i N V hb hN hη hδ p hp j da.1
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

theorem relative_roughness {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 4)
    {x : Gamma16Profile} (hx : x ∈ (sourceFamily N δ Δ V p j).labels) :
    ∀ q : ℕ, q.Prime → q ∣ gamma16Cofactor x → q.Coprime N →
      (N : ℝ) ^ (η / 10) ≤ (q : ℝ) := by
  have hx' : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j := (mem_filter.mp hx).1
  obtain ⟨hd,h3,h2,h1,_,_,hmask,_,_,_,_⟩ := profile_data hx'
  have g1 := hb.mother_window_large hN hη hδ p hp hd h1
  have g2 := hb.mother_window_large hN hη hδ p hp hd h2
  have g3 := hb.mother_window_large hN hη hδ p hp hd h3
  have hmask' : Sifted (x.1 * [x.2.2.2.1, x.2.2.1].prod * N)
      x.2.2.2.2 x.2.1 := by
    simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using hmask
  have hh := RelativeRoughness.masked_prefix [x.2.2.2.1, x.2.2.1] hmask' g3.2
    (fun q hq hqd => omega3_support_prime_lower _ (roughBox_window_tenth hb hN hη) hd hq hqd)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> assumption)
  have hlast : ∀ q : ℕ, q.Prime → q ∣ x.2.1 → q.Coprime N →
      (N : ℝ) ^ (η / 10) ≤ (q : ℝ) := by
    intro q hq hqd _
    have heq : q = x.2.1 := ((Nat.dvd_prime g3.1).mp hqd).resolve_left hq.ne_one
    simpa only [heq] using g3.2
  simpa only [gamma16Cofactor, List.prod_cons, List.prod_nil, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using RelativeRoughness.mul hh hlast

end Wu18938Campaign.M1.Confirmed.Four

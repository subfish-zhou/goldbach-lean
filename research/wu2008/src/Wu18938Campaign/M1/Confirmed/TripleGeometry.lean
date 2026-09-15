import Wu18938Campaign.M1.Confirmed.LabelledDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleErrorInputs

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Triple

open Wu2008DoubleSieve LowerTripleGrouped Finset Real
open scoped Classical

theorem geometry {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 6)
    {x : Label} (hx : x ∈ (sourceFamily N δ Δ V p j).labels) :
    PhysicalGeometry N (η / 10) (sourceFamily N δ Δ V p j) x := by
  obtain ⟨hd,_,hq,_⟩ := (mem_labels x).mp hx
  have hlarge := hb.mother_window_large hN hη hδ p hp hd hq
  have hg := (sourceFamily N δ Δ V p j).geometry x hx
  have hpos : 0 < cofactor x := hg.1
  have hqu : (x.2.2.1 : ℝ) ≤ (sourceFamily N δ Δ V p j).upper x :=
    (le_max_left _ _).trans hg.2.2.1
  have hcap : cofactor x * x.2.2.1 ≤ N := by
    exact_mod_cast (mul_le_mul_of_nonneg_left hqu (Nat.cast_nonneg (cofactor x))).trans hg.2.2.2
  have hle : cofactor x ≤ N := (Nat.le_mul_of_pos_right _ hlarge.1.pos).trans hcap
  have hpow : (N : ℝ) ^ (η / 10) ≤ cofactor x :=
    hlarge.2.trans (by exact_mod_cast Nat.le_of_dvd hpos (cofactor_divisors x).2.2)
  exact ⟨hpos,hle,hpow,omega3_cofactor_power_gap (by omega) hlarge.2 hcap,
    hg.2.1,hlarge.2.trans (le_max_left _ _),hg.2.2.1,hg.2.2.2⟩

theorem fixed_cofactor {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 6) (E : ℕ) :
    (∑ x ∈ (sourceFamily N δ Δ V p j).layerFibre E,
      (sourceFamily N δ Δ V p j).weight x) ≤
      (max 1 (1 / (η / 10))) ^ (m + 2) := by
  let S := (sourceFamily N δ Δ V p j).layerFibre E
  by_cases hs : S.Nonempty
  · obtain ⟨x,hx⟩ := hs
    have hg := geometry hb hN hη hδ p hp j (mem_filter.mp hx).1
    have he : cofactor x = E := (mem_filter.mp hx).2
    have hE : 0 < E := he ▸ hg.positive
    change (∑ x ∈ S, (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ)) ≤ _
    apply HighNonunit.weighted_labels_le _ S (fun x => x.1) fixedCofactorSelected
      hb.depth (by omega) hE (he ▸ hg.le_N) (by positivity : 0 < η / 10)
      (roughBox_window_tenth hb hN hη)
    · intro a ha
      rw [← (show cofactor a = E from (mem_filter.mp ha).2)]
      exact (cofactor_divisors a).1
    · intro a ha t
      have ham := (mem_filter.mp ha).1
      have hae : cofactor a = E := (mem_filter.mp ha).2
      obtain ⟨hd,hp',hq',_⟩ := (mem_labels a).mp ham
      have hpl := hb.mother_window_large hN hη hδ p hp hd hp'
      have hql := hb.mother_window_large hN hη hδ p hp hd hq'
      have hpd : a.2.1 ∣ E := hae ▸ (cofactor_divisors a).2.1
      have hqd : a.2.2.1 ∣ E := hae ▸ (cofactor_divisors a).2.2
      refine Fin.cases ?_ (fun _ => ?_) t
      · exact ⟨hpl.1,hpd,hpl.2⟩
      · exact ⟨hql.1,hqd,hql.2⟩
    · intro a ha b hb' hd ht
      apply fixedE_projection_injective hE (mem_filter.mp ha).2 (mem_filter.mp hb').2
      have hp' : a.2.1 = b.2.1 := congr_fun ht 0
      have hq' : a.2.2.1 = b.2.2.1 := congr_fun ht 1
      exact Prod.ext hd (Prod.ext hp' hq')
  · change (∑ x ∈ S, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

theorem fixed_output {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 6) (ell : ℕ) :
    (sourceFamily N δ Δ V p j).weightAt ell ≤
      (max 1 (1 / (η / 10))) ^ (m + 3) := by
  let L := sourceFamily N δ Δ V p j
  let S := L.labels.sigma fun x => (L.primes x).filter (fun r => N-cofactor x*r = ell)
  have data (a : Σ _ : Label, ℕ) (ha : a ∈ S) :
      a.1 ∈ L.labels ∧ a.2.Prime ∧ (N : ℝ) ^ (η / 10) ≤ (a.2 : ℝ) ∧
      cofactor a.1 * a.2 = N-ell := by
    obtain ⟨hx,hr,he⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    obtain ⟨_,hpr,hlo,_⟩ := mem_filter.mp hr
    have hg := geometry hb hN hη hδ p hp j hx
    have hcap := L.output_le hx hr
    refine ⟨hx,hpr,hg.lower_large.trans hlo.le,?_⟩
    change cofactor a.1 * a.2 ≤ N at hcap
    omega
  have heq : (∑ a ∈ S, (convolutionCoeff (convolutionWuWindows N Δ V) a.1.1 : ℝ)) =
      L.weightAt ell := by
    simp only [S, sum_sigma, sum_const, nsmul_eq_mul, LabelledPhysical.Family.weightAt]
    apply sum_congr rfl
    intro x _
    change _ * (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) =
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) * _
    exact mul_comm _ _
  rw [← heq]
  by_cases hs : S.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have da := data a ha
    have ga := geometry hb hN hη hδ p hp j da.1
    have hepos : 0 < N-ell := da.2.2.2 ▸ Nat.mul_pos ga.positive da.2.1.pos
    apply HighNonunit.weighted_labels_le (convolutionWuWindows N Δ V) S
      (fun a => a.1.1) LowerTripleGroupedOutput.selected hb.depth (by omega) hepos
      (Nat.sub_le N ell) (by positivity : 0 < η / 10) (roughBox_window_tenth hb hN hη)
    · intro a ha
      rw [← (data a ha).2.2.2]
      exact (cofactor_divisors a.1).1.trans (dvd_mul_right _ _)
    · intro a ha s
      have da := data a ha
      obtain ⟨hd,hp',hq',_⟩ := (mem_labels a.1).mp da.1
      have gp := hb.mother_window_large hN hη hδ p hp hd hp'
      have gq := hb.mother_window_large hN hη hδ p hp hd hq'
      have dp : a.1.2.1 ∣ N-ell := by
        rw [← da.2.2.2]
        exact (cofactor_divisors a.1).2.1.trans (dvd_mul_right _ _)
      have dq : a.1.2.2.1 ∣ N-ell := by
        rw [← da.2.2.2]
        exact (cofactor_divisors a.1).2.2.trans (dvd_mul_right _ _)
      have dr : a.2 ∣ N-ell := by rw [← da.2.2.2]; exact dvd_mul_left _ _
      refine Fin.cases ?_ (fun t => Fin.cases ?_ (fun u => Fin.cases ?_ (fun z => Fin.elim0 z) u) t) s
      · exact ⟨gp.1,dp,gp.2⟩
      · exact ⟨gq.1,dq,gq.2⟩
      · exact ⟨da.2.1,dr,da.2.2.1⟩
    · intro a ha b hb' hd ht
      have da := data a ha
      have db := data b hb'
      have hp' : a.1.2.1 = b.1.2.1 := congr_fun ht 0
      have hq : a.1.2.2.1 = b.1.2.2.1 := congr_fun ht 1
      have hr : a.2 = b.2 := congr_fun ht 2
      have hE : cofactor a.1 = cofactor b.1 := by
        apply Nat.eq_of_mul_eq_mul_right da.2.1.pos
        exact da.2.2.2.trans (by simpa only [← hr] using db.2.2.2.symm)
      have gx := geometry hb hN hη hδ p hp j da.1
      have hx : a.1 = b.1 := fixedE_projection_injective gx.positive rfl hE.symm
        (by simp only [hd,hp',hq])
      exact Sigma.ext hx (heq_of_eq hr)
  · rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

theorem relative_roughness {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 6)
    {x : Label} (hx : x ∈ (sourceFamily N δ Δ V p j).labels) :
    ∀ r : ℕ, r.Prime → r ∣ cofactor x → r.Coprime N → (N : ℝ) ^ (η / 10) ≤ (r : ℝ) := by
  obtain ⟨hd,hp',hq',_⟩ := (mem_labels x).mp hx
  have hpl := hb.mother_window_large hN hη hδ p hp hd hp'
  have hql := hb.mother_window_large hN hη hδ p hp hd hq'
  apply RelativeRoughness.of_sifted (source_mask p j hx).2 hql.2
  intro r hr hrd hc
  rcases hr.dvd_mul.mp hrd with hdp | hNr
  · rcases hr.dvd_mul.mp hdp with hdv | hpv
    · exact omega3_support_prime_lower _ (roughBox_window_tenth hb hN hη) hd hr hdv
    · have heq : r = x.2.1 := ((Nat.dvd_prime hpl.1).mp hpv).resolve_left hr.ne_one
      simpa only [heq] using hpl.2
  · exact (hr.coprime_iff_not_dvd.mp hc hNr).elim

end Wu18938Campaign.M1.Confirmed.Triple

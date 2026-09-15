import Wu08LargeQuadrature

noncomputable section
open Finset Real
open scoped Classical
open Wu2008DoubleSieve
namespace Wu08FirstPrimeFour.Large

/-- Closed enlargement only on the first coordinate; the actual strict integer
atom remains excluded from the large family and is not discarded. -/
def closedLabels (N : ℕ) (e : Bool) : Finset TruncatedFourPhysical.Quad :=
  (LastPrimeFour.fourClosedLabels N e).filter fun q => (N : ℝ)^(1/10 : ℝ) ≤ q.1

theorem closedLabels_subset (N : ℕ) (e : Bool) :
    closedLabels N e ⊆ FourRoughClosedMass.labels10 N ∪ FourRoughClosedMass.labels11 N := by
  intro q hq
  have h := (mem_filter.mp hq).1
  cases e
  · exact mem_union_left _ h
  · exact mem_union_right _ h

theorem actual_mass_le_closed (N : ℕ) (e : Bool) :
    (family N e).mass ≤ FourRoughClosedMass.mass N (closedLabels N e) := by
  let S := (family N e).labels.sigma fun t => (family N e).primes t
  have hm : (S.card : ℝ) = (family N e).mass := by
    simp only [S, card_sigma, Nat.cast_sum, LabelledPhysical.Family.mass]
    apply sum_congr rfl
    intro t _
    change (_ : ℝ) = 1 * _
    rw [one_mul]
  have hmap : Set.MapsTo LastPrimeFour.unswitch S
      ((closedLabels N e).sigma fun q => FourRoughClosedMass.cofactor N q) := by
    rintro ⟨⟨a,b,c,n⟩,d⟩ hx
    obtain ⟨ht,hd⟩ := mem_sigma.mp hx
    have ht' := mem_filter.mp ht
    have old : (⟨(a,b,c,n),d⟩ : Σ _ : LastPrimeFour.Index, ℕ) ∈
        LastPrimeFour.fourFullProfiles N e := mem_sigma.mpr ⟨ht'.1,hd⟩
    obtain ⟨hq,hn⟩ := mem_sigma.mp (LastPrimeFour.fourFullProfiles_maps old)
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨hq,ht'.2.le⟩,hn⟩
  have hc := card_le_card_of_injOn LastPrimeFour.unswitch hmap
    LastPrimeFour.unswitch_injective.injOn
  rw [← hm]
  have ht : ((((closedLabels N e).sigma fun q => FourRoughClosedMass.cofactor N q).card : ℕ) : ℝ) =
      FourRoughClosedMass.mass N (closedLabels N e) := by
    simp only [FourRoughClosedMass.mass,card_sigma,Nat.cast_sum]
  exact (show (S.card : ℝ) ≤ _ by exact_mod_cast hc).trans_eq ht

theorem closed_reciprocal_uniform :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool,
      FourRoughClosedMass.reciprocalMass (closedLabels N e) ≤ 625 := by
  obtain ⟨T,hT,h⟩ := FourRoughClosedMass.actual_reciprocal_uniform
  refine ⟨T,hT,?_⟩
  intro N hN e
  have hs : FourRoughClosedMass.reciprocalMass (closedLabels N e) ≤
      FourRoughClosedMass.reciprocalMass (LastPrimeFour.fourClosedLabels N e) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
  apply hs.trans
  cases e
  · exact (h N hN).1
  · exact (h N hN).2

/-- Full rough-count tolerance, including every closed atom, is paid before N
and uniformly for both original domains. -/
theorem actual_mass_main_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool,
      (family N e).mass ≤
        (FourRoughClosedMass.mainMass N (closedLabels N e)+ε)*((N : ℝ)/log N) := by
  let τ := ε*FourRoughClosedMass.alpha/625
  have ha := FourRoughClosedMass.fixed_geometry.2.1
  have ht : 0 < τ := div_pos (mul_pos hε ha) (by norm_num)
  obtain ⟨T1,hT1,h1⟩ := FourRoughClosedMass.actual_pointwise_upper ht
  obtain ⟨T2,_,h2⟩ := closed_reciprocal_uniform
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),?_⟩
  intro N hN e
  have hscale : 0 ≤ (N : ℝ)/log N := div_nonneg (Nat.cast_nonneg N)
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hs : FourRoughClosedMass.mass N (closedLabels N e) ≤
      ((N : ℝ)/log N)*(FourRoughClosedMass.mainMass N (closedLabels N e)+
        (τ/FourRoughClosedMass.alpha)*FourRoughClosedMass.reciprocalMass (closedLabels N e)) := by
    calc
      _ ≤ ∑ q ∈ closedLabels N e, ((N : ℝ)/log N)*
          (FourRoughClosedMass.mainTerm N q+(τ/FourRoughClosedMass.alpha)/fourModulusProduct q) :=
        sum_le_sum fun q hq => h1 N (by omega) q (closedLabels_subset N e hq)
      _ = _ := by
        rw [← mul_sum]
        congr 1
        simp only [FourRoughClosedMass.mainMass,FourRoughClosedMass.reciprocalMass,
          sum_add_distrib,mul_sum,mul_one_div]
  have herr : (τ/FourRoughClosedMass.alpha)*
      FourRoughClosedMass.reciprocalMass (closedLabels N e) ≤ ε := by
    calc
      _ ≤ (τ/FourRoughClosedMass.alpha)*625 :=
        mul_le_mul_of_nonneg_left (h2 N (by omega) e) (div_nonneg ht.le ha.le)
      _ = ε := by dsimp [τ]; field_simp [ha.ne']
  exact (actual_mass_le_closed N e).trans (hs.trans
    ((mul_le_mul_of_nonneg_left (add_le_add_right herr _) hscale).trans_eq (mul_comm _ _)))

#print axioms actual_mass_main_paid
end Wu08FirstPrimeFour.Large

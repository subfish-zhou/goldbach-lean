import MathlibNt.Wu2008DoubleSieve.TruncatedFourPhysical

/-! Positive-complement fibres pay every exceptional original label. -/
namespace Wu2008DoubleSieve.TruncatedFourPhysical
open Finset Real
open scoped Classical

noncomputable def exceptionalOutputs (N : ℕ) (X : ℝ) : Finset ℕ :=
  N.primeFactors ∪ (Icc 1 ⌊X⌋₊).image (fun k => N-k)

theorem exceptional_maps {N : ℕ} {z w V X : ℝ} {S : Finset Quad}
    (hN : 4 ≤ N) (hS : S ⊆ fourModulusDomain N z w V)
    (hcap : ∀ t ∈ S, (fourModulusProduct t : ℝ) ≤ X) :
    Set.MapsTo (fun x : Label => x.2) (exceptional N S) (exceptionalOutputs N X) := by
  intro x hx
  obtain ⟨hx,hbad⟩ := mem_filter.mp hx
  obtain ⟨ht,hpN,hp,_,_⟩ := raw_mem hx
  apply mem_union.mpr
  rcases hbad with hb | hu
  · exact Or.inl (Nat.mem_primeFactors.mpr ⟨hp,hb,by omega⟩)
  · right
    apply mem_image.mpr
    refine ⟨fourModulusProduct x.1, mem_Icc.mpr ⟨?_, Nat.le_floor (hcap _ ht)⟩, ?_⟩
    · exact domain_product_pos (hS ht)
    · rw [← hu, Nat.sub_sub_self hpN]

theorem exceptionalOutputs_card {N : ℕ} {X : ℝ} (hX : 0 ≤ X) :
    ((exceptionalOutputs N X).card : ℝ) ≤ sqrt N + 1 + X := by
  have hh : (exceptionalOutputs N X).card ≤ N.primeFactors.card + ⌊X⌋₊ := by
    calc
      _ ≤ N.primeFactors.card + ((Icc 1 ⌊X⌋₊).image (fun k => N-k)).card := card_union_le _ _
      _ ≤ N.primeFactors.card + (Icc 1 ⌊X⌋₊).card := Nat.add_le_add_left (card_image_le) _
      _ = _ := by rw [Nat.card_Icc]; omega
  have hr : ((exceptionalOutputs N X).card : ℝ) ≤ (N.primeFactors.card : ℝ) + ⌊X⌋₊ :=
    by exact_mod_cast hh
  exact hr.trans (add_le_add (primeFactors_card_le_sqrt_add_one N) (Nat.floor_le hX))

/-- The injection remembers all four slots, even when different labels have
identical product. No product-image cardinality is used. -/
theorem exceptional_fibre {N p : ℕ} {κ w V : ℝ} {S : Finset Quad}
    (hN : 4 ≤ N) (he : Even N) (hκ : 0 < κ)
    (hS : S ⊆ fourModulusDomain N ((N : ℝ)^κ) w V) :
    (((exceptional N S).filter (fun x => x.2 = p)).card : ℝ) ≤ (1/κ)^4 := by
  let F := (exceptional N S).filter (fun x => x.2 = p)
  by_cases hF : F.Nonempty
  · obtain ⟨x,hx⟩ := hF
    obtain ⟨hx,hxp⟩ := mem_filter.mp hx
    obtain ⟨_,hpN,hp,_,_⟩ := raw_mem (mem_filter.mp hx).1
    rw [hxp] at hpN hp
    have hpLt := prime_lt_even hN he hp hpN
    have hinj : Set.InjOn (fun x : Label => x.1) F := by
      rintro ⟨t,q⟩ hx ⟨u,r⟩ hy h
      have hq := (mem_filter.mp hx).2
      have hr := (mem_filter.mp hy).2
      dsimp only at h hq hr
      subst u
      subst q
      subst r
      rfl
    have hmaps : Set.MapsTo (fun x : Label => x.1) F
        ((fourModulusDomain N ((N : ℝ)^κ) w V).filter
          (fun t => fourModulusProduct t ∣ N-p)) := by
      intro y hy
      obtain ⟨hy,hyp⟩ := mem_filter.mp hy
      obtain ⟨ht,_,_,hd,_⟩ := raw_mem (mem_filter.mp hy).1
      rw [hyp] at hd
      exact mem_filter.mpr ⟨hS ht,hd⟩
    have hc := card_le_card_of_injOn (fun x : Label => x.1) hmaps hinj
    exact (show (F.card : ℝ) ≤ _ by exact_mod_cast hc).trans
      (fourModulus_divisor_fibre_le (by omega) (Nat.sub_pos_of_lt hpLt)
        (Nat.sub_le _ _) hκ)
  · have hz : F = ∅ := not_nonempty_iff_eq_empty.mp hF
    change (F.card : ℝ) ≤ _
    rw [hz, card_empty, Nat.cast_zero]
    positivity

theorem exceptional_bound {N : ℕ} {κ w V X : ℝ} {S : Finset Quad}
    (hN : 4 ≤ N) (he : Even N) (hκ : 0 < κ) (hX : 0 ≤ X)
    (hS : S ⊆ fourModulusDomain N ((N : ℝ)^κ) w V)
    (hcap : ∀ t ∈ S, (fourModulusProduct t : ℝ) ≤ X) :
    ((exceptional N S).card : ℝ) ≤ (1/κ)^4 * (sqrt N + 1 + X) := by
  have hc := card_eq_sum_card_fiberwise (exceptional_maps hN hS hcap)
  rw [hc, Nat.cast_sum]
  calc
    _ ≤ ∑ _p ∈ exceptionalOutputs N X, (1/κ)^4 :=
      sum_le_sum (fun _ _ => exceptional_fibre hN he hκ hS)
    _ = (1/κ)^4 * ((exceptionalOutputs N X).card : ℝ) := by
      rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (exceptionalOutputs_card hX) (by positivity)

/-- Finite physical reduction, before any asymptotic payment. -/
theorem source_le_physical_finite {N : ℕ} {κ w V X : ℝ} {S : Finset Quad}
    (hN : 4 ≤ N) (he : Even N) (hκ : 0 < κ) (hX : 0 ≤ X)
    (hS : S ⊆ fourModulusDomain N ((N : ℝ)^κ) w V)
    (hcap : ∀ t ∈ S, (fourModulusProduct t : ℝ) ≤ X) :
    ((∑ t ∈ S, sieveCount N (fourModulusProduct t) N (t.2.1 : ℝ) : ℤ) : ℝ) ≤
      (physical N S).card + (1/κ)^4 * (sqrt N + 1 + X) := by
  rw [source_cast]
  have hh : ((raw N S).card : ℝ) ≤ (physical N S).card + (exceptional N S).card :=
    by exact_mod_cast raw_le_physical_exceptional (S := S) hN he
  exact hh.trans (add_le_add le_rfl (exceptional_bound hN he hκ hX hS hcap))

end Wu2008DoubleSieve.TruncatedFourPhysical

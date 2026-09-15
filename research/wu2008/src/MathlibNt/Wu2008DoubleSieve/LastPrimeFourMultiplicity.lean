import MathlibNt.Wu2008DoubleSieve.LastPrimeFourProfiles

/-! Fixed Cartesian prime-divisor multiplicity, with the rough quotient
recovered by cancellation. No primality of the quotient is used. -/
namespace Wu2008DoubleSieve.LastPrimeFour
open Finset Real
open scoped Classical

def triple (t : Index) : Fin 3 → ℕ := ![t.1,t.2.1,t.2.2.1]

noncomputable def layerBound : ℕ := ⌈(1 / truncatedSixthLowerAlpha)^ (3 : ℕ)⌉₊

theorem triple_fibre_injective {N : ℕ} {e : Bool} (m : ℕ) :
    Set.InjOn triple ((family N e).layerFibre m) := by
  rintro ⟨a,b,c,n⟩ hx ⟨a',b',c',n'⟩ hy ht
  obtain ⟨hx,hmx⟩ := mem_filter.mp hx
  obtain ⟨hy,hmy⟩ := mem_filter.mp hy
  have ha : a = a' := congrFun ht 0
  have hb : b = b' := congrFun ht 1
  have hc : c = c' := congrFun ht 2
  subst a'; subst b'; subst c'
  obtain ⟨hpa,_,_,hpb,_,hpc,_⟩ := base_data (labels_base hx)
  have hn : n = n' := Nat.mul_left_cancel
    (Nat.mul_pos (Nat.mul_pos hpa.pos hpb.pos) hpc.pos) (hmx.trans hmy.symm)
  subst n'
  rfl

theorem triple_large_divisors {N : ℕ} {e : Bool} {t : Index}
    (ht : t ∈ labels N e) : ∀ j : Fin 3,
    (triple t j).Prime ∧ triple t j ∣ cofactor t ∧
      (N : ℝ)^truncatedSixthLowerAlpha ≤ triple t j := by
  obtain ⟨ha,_,hza,hb,_,hc,_,hab,hbc,_⟩ := base_data (labels_base ht)
  have hzb : (N : ℝ)^truncatedSixthLowerAlpha ≤ t.2.1 :=
    hza.trans (by exact_mod_cast hab.le)
  have hzc : (N : ℝ)^truncatedSixthLowerAlpha ≤ t.2.2.1 :=
    hzb.trans (by exact_mod_cast hbc.le)
  have hda : t.1 ∣ cofactor t := by
    exact (dvd_mul_right t.1 t.2.1).trans
      ((dvd_mul_right _ t.2.2.1).trans (dvd_mul_right _ t.2.2.2))
  have hdb : t.2.1 ∣ cofactor t := by
    exact (dvd_mul_left t.2.1 t.1).trans
      ((dvd_mul_right _ t.2.2.1).trans (dvd_mul_right _ t.2.2.2))
  have hdc : t.2.2.1 ∣ cofactor t :=
    (dvd_mul_left t.2.2.1 (t.1*t.2.1)).trans (dvd_mul_right _ t.2.2.2)
  simp only [triple, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.forall_fin_zero, and_true]
  exact ⟨⟨ha,hda,hza⟩,⟨hb,hdb,hzb⟩,hc,hdc,hzc⟩

/-- The common bound is a constant depending only on the original fixed alpha,
not on N, on the AP modulus, on the rough residual, or on a label. -/
theorem fibre_card_le {N : ℕ} (hN : 1 < N) (e : Bool) (m : ℕ) :
    ((family N e).layerFibre m).card ≤ layerBound := by
  by_cases hh : ((family N e).layerFibre m).Nonempty
  · obtain ⟨t,ht⟩ := hh
    obtain ⟨ht,hmt⟩ := mem_filter.mp ht
    have hpos : 0 < m := hmt ▸ (label_geometry ht).1
    have hle : m ≤ N := hmt ▸ label_le_N ht
    have hc := omega3_prime_labels_card_le ((family N e).layerFibre m) triple
      (triple_fibre_injective m) hN hpos hle
      (by norm_num [truncatedSixthLowerAlpha] : 0 < truncatedSixthLowerAlpha)
      (by
        intro t ht j
        obtain ⟨ht,hmt⟩ := mem_filter.mp ht
        change cofactor t = m at hmt
        simpa only [← hmt] using triple_large_divisors ht j)
    exact_mod_cast hc.trans (Nat.le_ceil ((1/truncatedSixthLowerAlpha)^(3 : ℕ)))
  · rw [not_nonempty_iff_eq_empty.mp hh, card_empty]
    exact Nat.zero_le _

/-- Exact signed regrouping keeps all labels, endpoints, and the prime-count
center; layer choices depend on N and the family only, never on q. -/
theorem signed_eq_layers {N : ℕ} (hN : 1 < N) (e : Bool) (q : ℕ) :
    (∑ t ∈ (labels N e).filter (fun t => (cofactor t).Coprime q),
      omega3ProfileError N q (cofactor t) (lower N e t) (upper N e t)) =
      ∑ j ∈ range layerBound, (family N e).layerReduced (0,0,0,0) j q := by
  have h := (family N e).reduced_eq_layers (0,0,0,0) layerBound (fibre_card_le hN e) q
  change (∑ t ∈ (labels N e).filter (fun t => (cofactor t).Coprime q),
    1 * omega3ProfileError N q (cofactor t) (lower N e t) (upper N e t)) = _ at h
  simpa only [one_mul] using h

end Wu2008DoubleSieve.LastPrimeFour

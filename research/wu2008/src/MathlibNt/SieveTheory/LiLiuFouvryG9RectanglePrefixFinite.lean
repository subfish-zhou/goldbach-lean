import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedMass

noncomputable section
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Expanding the actual mass retains every ordered long label, including
multiplicities of equal products. No coprimality is imposed on the third prime. -/
theorem fouvryG9RectanglePrefix_mass_labels (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) :
    fouvryG9RectangleMass N ρ k =
      ∑ n ∈ fouvryG9RectanglePrimeSupport N ρ k,
        ∑ _z ∈ fouvryG9LongLabels N ρ k, fouvryG9RectangleBeta N n := by
  unfold fouvryG9RectangleMass
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  exact (fouvryG9Long_sum N ρ k (fun n _ => fouvryG9RectangleBeta N n) n).symm

/-- Half-open geometric intervals have unique natural indices. -/
theorem fouvryG9RectanglePrefix_index_unique {ρ x : ℝ} (hρ : 1 < ρ)
    {i j : ℕ} (hi : ρ^i ≤ x ∧ x < ρ^(i+1))
    (hj : ρ^j ≤ x ∧ x < ρ^(j+1)) : i = j := by
  apply le_antisymm
  · by_contra h
    have hji : j+1 ≤ i := by omega
    have hp := pow_le_pow_right₀ hρ.le hji
    exact (not_lt_of_ge (hp.trans hi.1)) hj.2
  · by_contra h
    have hij : i+1 ≤ j := by omega
    have hp := pow_le_pow_right₀ hρ.le hij
    exact (not_lt_of_ge (hp.trans hj.1)) hi.2

/-- The actual weighted mass is exactly the number of ordered rectangle labels. -/
theorem fouvryG9RectanglePrefix_mass_eq_card {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (k : ℕ × ℕ × ℕ) (hbig : 3 ≤ ρ^k.1)
    (hne : (fouvryG9GridCell N e ρ k).Nonempty) :
    fouvryG9RectangleMass N ρ k =
      ((fouvryG9LongShortLabels N ρ k ×ˢ fouvryG9LongLabels N ρ k).card : ℝ) := by
  have h := fouvryG9LongShortLabels_sum_interval hN hρ hρu k hbig hne
    (fun _ => ((fouvryG9LongLabels N ρ k).card : ℝ))
  change (∑ _n ∈ fouvryG9LongShortLabels N ρ k,
    ((fouvryG9LongLabels N ρ k).card : ℝ)) =
    ∑ n ∈ fouvryG9RectanglePrimeSupport N ρ k,
      fouvryG9RectangleBeta N n * ((fouvryG9LongLabels N ρ k).card : ℝ) at h
  rw [fouvryG9RectanglePrefix_mass_labels]
  simpa [sum_const, nsmul_eq_mul, card_product, Nat.cast_mul, mul_comm] using h.symm

/-- A labelled triple can occur in at most one rectangle. This prevents
counting the same third-prime prefix once per occupied cell. -/
theorem fouvryG9RectanglePrefix_label_unique {N : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    {k k' : ℕ × ℕ × ℕ} {n : ℕ} {z : ℕ × ℕ}
    (hn : n ∈ fouvryG9LongShortLabels N ρ k)
    (hz : z ∈ fouvryG9LongLabels N ρ k)
    (hn' : n ∈ fouvryG9LongShortLabels N ρ k')
    (hz' : z ∈ fouvryG9LongLabels N ρ k') : k = k' := by
  obtain ⟨_, _, _, _, _, hnlo, hnhi⟩ := mem_filter.mp hn
  obtain ⟨_, _, _, _, _, hnlo', hnhi'⟩ := mem_filter.mp hn'
  obtain ⟨_, _, _, _, _, hslo, hshi, htlo, hthi⟩ := mem_filter.mp hz
  obtain ⟨_, _, _, _, _, hslo', hshi', htlo', hthi'⟩ := mem_filter.mp hz'
  exact Prod.ext (fouvryG9RectanglePrefix_index_unique hρ ⟨hnlo, hnhi⟩ ⟨hnlo', hnhi'⟩)
    (Prod.ext (fouvryG9RectanglePrefix_index_unique hρ ⟨hslo, hshi⟩ ⟨hslo', hshi'⟩)
      (fouvryG9RectanglePrefix_index_unique hρ ⟨htlo, hthi⟩ ⟨htlo', hthi'⟩))

/-- Occupancy enlarges both curved bounds by rho cubed. In particular the
original pair curve is NOT imposed on the enlarged rectangle. -/
theorem fouvryG9RectanglePrefix_enlarged_geometry {N : ℕ} {e ρ : ℝ}
    (hρ : 1 < ρ) {k : ℕ × ℕ × ℕ}
    (hne : (fouvryG9GridCell N e ρ k).Nonempty)
    {n : ℕ} {z : ℕ × ℕ} (hn : n ∈ fouvryG9LongShortLabels N ρ k)
    (hz : z ∈ fouvryG9LongLabels N ρ k) :
    (n : ℝ)*z.1*z.2 < ρ^3*(N : ℝ) ∧
      (n : ℝ)*(z.1 : ℝ)^2 ≤ ρ^3*(N : ℝ) := by
  obtain ⟨y, hy⟩ := hne
  have hyc := (fouvryG9GridCell_mem_iff.mp hy).1
  have hg := fouvryG9Carrier_geometry hyc
  have hyn := fouvryG9LongShortLabels_of_cell hρ hy
  have hyz := fouvryG9LongLabels_of_cell hρ hy
  obtain ⟨_, hnprime, _, _, _, _, hnhi⟩ := mem_filter.mp hn
  obtain ⟨_, hsprime, htprime, _, _, _, hshi, _, hthi⟩ := mem_filter.mp hz
  obtain ⟨_, _, _, _, _, hylo, _⟩ := mem_filter.mp hyn
  obtain ⟨_, _, _, _, _, hyslo, _, hytlo, _⟩ := mem_filter.mp hyz
  have hr : 0 < ρ := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnprime.pos
  have hs0 : (0 : ℝ) < z.1 := by exact_mod_cast hsprime.pos
  have ht0 : (0 : ℝ) < z.2 := by exact_mod_cast htprime.pos
  have an : (n : ℝ) < ρ*(y.2.2 : ℝ) := by
    rw [pow_succ] at hnhi
    exact hnhi.trans_le (by nlinarith [mul_le_mul_of_nonneg_left hylo hr.le])
  have bs : (z.1 : ℝ) < ρ*(y.2.1 : ℝ) := by
    rw [pow_succ] at hshi
    exact hshi.trans_le (by nlinarith [mul_le_mul_of_nonneg_left hyslo hr.le])
  have ct : (z.2 : ℝ) < ρ*((y.1 / y.2.1 : ℕ) : ℝ) := by
    rw [pow_succ] at hthi
    exact hthi.trans_le (by nlinarith [mul_le_mul_of_nonneg_left hytlo hr.le])
  have ab := mul_lt_mul an bs.le hs0 (le_of_lt (hn0.trans an))
  have abc := mul_lt_mul ab ct.le ht0 (le_of_lt ((mul_pos hn0 hs0).trans ab))
  have abb := mul_lt_mul ab bs.le hs0 (le_of_lt ((mul_pos hn0 hs0).trans ab))
  have hm : (y.2.1 : ℝ)*((y.1 / y.2.1 : ℕ) : ℝ) = y.1 := by
    exact_mod_cast Nat.mul_div_cancel' hg.2.2.1
  have hprod : (y.2.2 : ℝ)*y.1 < N := by
    exact_mod_cast hg.2.2.2.2.2.2.2.2.2.2
  have hcurve : (y.2.2 : ℝ)*(y.2.1 : ℝ)^2 ≤ N := by
    exact_mod_cast hg.2.2.2.2.2.2.2.2.1
  constructor
  · calc
      _ < ρ^3*((y.2.2 : ℝ)*y.1) := by
        calc
          _ < (ρ*(y.2.2 : ℝ)*(ρ*(y.2.1 : ℝ)))*(ρ*((y.1/y.2.1 : ℕ) : ℝ)) := abc
          _ = _ := by rw [show ρ^3*((y.2.2 : ℝ)*y.1) =
              ρ^3*((y.2.2 : ℝ)*((y.2.1 : ℝ)*((y.1/y.2.1 : ℕ) : ℝ))) by rw [hm]]; ring
      _ < _ := mul_lt_mul_of_pos_left hprod (pow_pos hr 3)
  · calc
      _ ≤ ρ^3*((y.2.2 : ℝ)*(y.2.1 : ℝ)^2) := by nlinarith only [abb]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcurve (pow_nonneg hr.le 3)

/-- Every occupied rectangular label lands in the parent's exact relaxed pair
carrier and in one true prime prefix. -/
theorem fouvryG9RectanglePrefix_pair_and_prefix {N : ℕ} {e ρ : ℝ}
    (hρ : 1 < ρ) {k : ℕ × ℕ × ℕ}
    (hne : (fouvryG9GridCell N e ρ k).Nonempty)
    {n : ℕ} {z : ℕ × ℕ} (hn : n ∈ fouvryG9LongShortLabels N ρ k)
    (hz : z ∈ fouvryG9LongLabels N ρ k) :
    (n,z.1) ∈ fouvryG9RelaxedPairs N ρ ∧ z.2.Prime ∧
      (z.2 : ℝ) ≤ ρ^3*(N : ℝ)/((n : ℝ)*z.1) ∧
      (z.1 : ℝ) ≤ ρ^3*(N : ℝ)/((n : ℝ)*z.1) := by
  have hg := fouvryG9RectanglePrefix_enlarged_geometry hρ hne hn hz
  obtain ⟨hnN, hnp, _, hna, hnb, _⟩ := mem_filter.mp hn
  obtain ⟨hzN, hsp, htp, _, hsa, _⟩ := mem_filter.mp hz
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnp.pos
  have hs0 : (0 : ℝ) < z.1 := by exact_mod_cast hsp.pos
  refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hnN, (mem_product.mp hzN).1⟩,
    hnp, hsp, hna, hnb, hsa, hg.2⟩, htp, ?_, ?_⟩
  · apply (le_div_iff₀ (mul_pos hn0 hs0)).mpr
    nlinarith only [hg.1]
  · apply (le_div_iff₀ (mul_pos hn0 hs0)).mpr
    nlinarith only [hg.2]

/-- The third-prime labels in an occupied rectangle, with the first two
labels fixed. Keeping the cell index until the injection proves no duplication. -/
def fouvryG9RectanglePrefixThirds (N : ℕ) (ρ : ℝ) (n s : ℕ)
    (k : ℕ × ℕ × ℕ) : Finset ℕ :=
  (range (N+1)).filter fun t =>
    n ∈ fouvryG9LongShortLabels N ρ k ∧ (s,t) ∈ fouvryG9LongLabels N ρ k

/-- All occupied third boxes merge into ONE prime prefix, not one prefix per
cell. This is a finite injection and uses no prime-number theorem. -/
theorem fouvryG9RectanglePrefix_thirds_sum_le {N : ℕ} {e ρ : ℝ}
    (hρ : 1 < ρ) (n s : ℕ) :
    (∑ k ∈ fouvryG9GridUsed N e ρ, (fouvryG9RectanglePrefixThirds N ρ n s k).card) ≤
      ((range (⌊ρ^3*(N : ℝ)/((n : ℝ)*s)⌋₊+1)).filter Nat.Prime).card := by
  classical
  rw [← card_sigma]
  apply card_le_card_of_injOn (fun q => q.2)
  · intro q hq
    obtain ⟨hk, ht⟩ := mem_sigma.mp hq
    obtain ⟨_, hn, hz⟩ := mem_filter.mp ht
    have hp := fouvryG9RectanglePrefix_pair_and_prefix hρ
      (fouvryG9GridCell_nonempty_iff.mpr hk) hn hz
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, hp.2.1⟩
    have hfloor : q.2 ≤ ⌊ρ^3*(N : ℝ)/((n : ℝ)*s)⌋₊ :=
      Nat.le_floor hp.2.2.1
    exact Nat.lt_succ_of_le hfloor
  · intro q hq r hr he
    obtain ⟨_, hqt⟩ := mem_sigma.mp hq
    obtain ⟨_, hrt⟩ := mem_sigma.mp hr
    obtain ⟨_, hqn, hqz⟩ := mem_filter.mp hqt
    obtain ⟨_, hrn, hrz⟩ := mem_filter.mp hrt
    have hqz' : (s, r.2) ∈ fouvryG9LongLabels N ρ q.1 := by simpa only [he] using hqz
    have hk := fouvryG9RectanglePrefix_label_unique hρ hqn hqz' hrn hrz
    exact Sigma.ext hk (heq_of_eq he)

#print axioms fouvryG9RectanglePrefix_thirds_sum_le
#print axioms fouvryG9RectanglePrefix_enlarged_geometry
#print axioms fouvryG9RectanglePrefix_pair_and_prefix
#print axioms fouvryG9RectanglePrefix_label_unique
#print axioms fouvryG9RectanglePrefix_mass_labels
#print axioms fouvryG9RectanglePrefix_mass_eq_card
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

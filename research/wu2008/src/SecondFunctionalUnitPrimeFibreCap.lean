import SecondFunctionalUnitPrimeFibreReweight

open scoped BigOperators Classical Topology
namespace SecondFunctionalUnitPrimeFibre
open Wu2008DoubleSieve LiLiuPrereqBuchstab Real Finset Filter

/-- Only the cap is made strict; the product gate remains closed. -/
noncomputable def strictPhysical (B X q H : ℝ) : Finset ℕ :=
  (physical B X q H).filter (fun p => (p : ℝ) < H)
noncomputable def capAtom (B X q H : ℝ) : Finset ℕ :=
  (physical B X q H).filter (fun p => (p : ℝ) = H)

theorem mem_strictPhysical {B X q H : ℝ} (hH : 0 ≤ H) {p : ℕ} :
    p ∈ strictPhysical B X q H ↔
      p.Prime ∧ q < (p : ℝ) ∧ (p : ℝ) < H ∧ B * (p : ℝ) ≤ X := by
  simp only [strictPhysical, physical, mem_filter, mem_primesIcc hH]
  constructor
  · rintro ⟨⟨⟨hp, _, _⟩, hq, hx⟩, hh⟩; exact ⟨hp,hq,hh,hx⟩
  · rintro ⟨hp,hq,hh,hx⟩; exact ⟨⟨⟨hp,Nat.cast_nonneg _,hh.le⟩,hq,hx⟩,hh⟩

theorem mem_capAtom {B X q H : ℝ} (hH : 0 ≤ H) {p : ℕ} :
    p ∈ capAtom B X q H ↔
      p.Prime ∧ q < (p : ℝ) ∧ (p : ℝ) = H ∧ B * (p : ℝ) ≤ X := by
  simp only [capAtom, physical, mem_filter, mem_primesIcc hH]
  constructor
  · rintro ⟨⟨⟨hp, _, _⟩, hq, hx⟩, hh⟩; exact ⟨hp,hq,hh,hx⟩
  · rintro ⟨hp,hq,hh,hx⟩; exact ⟨⟨⟨hp,Nat.cast_nonneg _,hh.le⟩,hq,hx⟩,hh⟩

theorem cap_partition {B X q H : ℝ} (hH : 0 ≤ H) :
    physical B X q H = strictPhysical B X q H ∪ capAtom B X q H ∧
    Disjoint (strictPhysical B X q H) (capAtom B X q H) := by
  constructor
  · ext p
    simp only [strictPhysical, capAtom, mem_union, mem_filter]
    constructor
    · intro hp
      have hh := ((mem_primesIcc hH).mp (mem_filter.mp hp).1).2.2
      rcases hh.lt_or_eq with hl | he
      · exact Or.inl ⟨hp,hl⟩
      · exact Or.inr ⟨hp,he⟩
    · rintro (⟨hp,_⟩ | ⟨hp,_⟩) <;> exact hp
  · apply disjoint_left.mpr
    intro p hp hq
    have hl := (mem_filter.mp hp).2
    have he := (mem_filter.mp hq).2
    exact (ne_of_lt hl) he

theorem cap_card_le_one (B X q H : ℝ) : (capAtom B X q H).card ≤ 1 := by
  apply card_le_one.mpr
  intro p hp r hr
  have h1 := (mem_filter.mp hp).2
  have h2 := (mem_filter.mp hr).2
  exact_mod_cast h1.trans h2.symm

theorem cap_card_difference {B X q H : ℝ} (hH : 0 ≤ H) :
    ((physical B X q H).card : ℝ) - ((strictPhysical B X q H).card : ℝ) =
      ((capAtom B X q H).card : ℝ) := by
  have hh := congrArg Finset.card (cap_partition (B := B) (X := X) (q := q) hH).1
  rw [card_union_of_disjoint (cap_partition hH).2] at hh
  have hh' : ((physical B X q H).card : ℝ) =
      ((strictPhysical B X q H).card : ℝ) + ((capAtom B X q H).card : ℝ) := by exact_mod_cast hh
  linarith

/-- The decay exponent follows from an actual cap member, not a count bound. -/
theorem cap_geometry {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin m → primeSlabPrimes R) (j : Fin m) (phi b : ℝ)
    (hp : (capAtom (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).Nonempty) :
    b ≤ phi - ∑ i, coordinate f i := by
  obtain ⟨p,hp⟩ := hp
  have hm := (mem_capAtom (rpow_nonneg (by linarith : 0 ≤ R) _)).mp hp
  have hh : R ^ b ≤ R ^ phi / prefixProduct f := by
    apply (le_div_iff₀ (prefixProduct_pos hR f)).mpr
    rw [← hm.2.2.1]
    simpa only [mul_comm] using hm.2.2.2
  rw [prefixProduct_power hR f, ← rpow_sub (by linarith : 0 < R)] at hh
  exact (rpow_le_rpow_left_iff hR).mp hh

/-- Normalized per-prefix atom. The empty case requires no geometric/PNT inference. -/
theorem cap_weight_bound {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin m → primeSlabPrimes R) (j : Fin m) (phi b a : ℝ)
    (hel : a ≤ coordinate f j) (heb : coordinate f j ≤ b) :
    0 ≤ log R * R ^ (-(phi - ∑ i, coordinate f i)) *
      ((capAtom (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ) ∧
    log R * R ^ (-(phi - ∑ i, coordinate f i)) *
      ((capAtom (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ) ≤
        log R * R ^ (-a) := by
  have hR0 : 0 ≤ R := by linarith
  have hs : 0 ≤ log R * R ^ (-(phi - ∑ i, coordinate f i)) :=
    mul_nonneg (log_pos hR).le (rpow_nonneg hR0 _)
  refine ⟨mul_nonneg hs (Nat.cast_nonneg _), ?_⟩
  by_cases hp : (capAtom (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).Nonempty
  · have hg := cap_geometry hR f j phi b hp
    have hc : ((capAtom (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ) ≤ 1 := by
      exact_mod_cast cap_card_le_one (prefixProduct f) (R ^ phi) (f j).val (R ^ b)
    calc
      _ ≤ log R * R ^ (-(phi - ∑ i, coordinate f i)) := by simpa using mul_le_mul_of_nonneg_left hc hs
      _ ≤ log R * R ^ (-a) := mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_exponent_le hR.le (neg_le_neg (hel.trans (heb.trans hg)))) (log_pos hR).le
  · rw [Finset.not_nonempty_iff_eq_empty.mp hp]
    simp only [card_empty, Nat.cast_zero, mul_zero]
    exact mul_nonneg (log_pos hR).le (rpow_nonneg hR0 _)

/-- Exact finite reciprocal payment of closed-cap atoms over any labelled subset. -/
theorem cap_sum_bound {m : ℕ} {R : ℝ} (hR : 1 < R)
    (S : Finset (Fin m → primeSlabPrimes R)) (j : Fin m) (phi b a : ℝ)
    (hS : ∀ f ∈ S, a ≤ coordinate f j ∧ coordinate f j ≤ b) :
    0 ≤ log R / R ^ phi *
      (∑ f ∈ S, (((physical (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ) -
        ((strictPhysical (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ))) ∧
    log R / R ^ phi *
      (∑ f ∈ S, (((physical (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ) -
        ((strictPhysical (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ))) ≤
      (log R * R ^ (-a)) * (∑ f ∈ S, primeSlabWeight R f) := by
  have hR0 : 0 < R := by linarith
  simp_rw [cap_card_difference (rpow_nonneg hR0.le b)]
  have heq (f : Fin m → primeSlabPrimes R) :
      log R / R ^ phi * ((capAtom (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ) =
      primeSlabWeight R f * (log R * R ^ (-(phi - ∑ i, coordinate f i)) *
        ((capAtom (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ)) := by
    rw [reciprocal_product, prefixProduct_power hR f, neg_sub, rpow_sub hR0]
    field_simp [ne_of_gt (rpow_pos_of_pos hR0 (∑ i, coordinate f i))]
  rw [mul_sum]
  simp_rw [heq]
  constructor
  · apply sum_nonneg
    intro f hf
    exact mul_nonneg (by unfold primeSlabWeight; positivity) (cap_weight_bound hR f j phi b a (hS f hf).1 (hS f hf).2).1
  · rw [mul_sum]
    apply sum_le_sum
    intro f hf
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (cap_weight_bound hR f j phi b a (hS f hf).1 (hS f hf).2).2
      (show 0 ≤ primeSlabWeight R f by unfold primeSlabWeight; positivity)

/-- The literal closed-minus-strict count is nonnegative and at most one. -/
theorem cap_count_bounds {B X q H : ℝ} (hH : 0 ≤ H) :
    0 ≤ ((physical B X q H).card : ℝ) - ((strictPhysical B X q H).card : ℝ) ∧
    ((physical B X q H).card : ℝ) - ((strictPhysical B X q H).card : ℝ) ≤ 1 := by
  rw [cap_card_difference hH]
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast cap_card_le_one B X q H⟩

/-- Actual cube mass is bounded internally; no caller-supplied mass hypothesis. -/
theorem cap_sum_eventually :
    ∀ᶠ R : ℝ in atTop, ∀ (m : ℕ) (S : Finset (Fin m → primeSlabPrimes R))
      (j : Fin m) (phi b a : ℝ),
      (∀ f ∈ S, a ≤ coordinate f j ∧ coordinate f j ≤ b) →
      log R / R ^ phi *
        (∑ f ∈ S, (((physical (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ) -
          ((strictPhysical (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ))) ≤
        5 ^ m * (log R * R ^ (-a)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).eventually
      (eventually_ge_atTop primeOrderedMertensStart),
    primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with R hR hs he
  intro m S j phi b a hS
  have hm := primeSlab_interval_mass hR hs
    (by norm_num : (1/10 : ℝ) ≤ 1/10) (by norm_num : (1/10 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1/2)
  have hm5 : (∑ p ∈ primeSlabPrimes R, 1/(p : ℝ)) ≤ 5 := by
    unfold primeSlabPrimes
    linarith
  have hsubset : (∑ f ∈ S, primeSlabWeight R f) ≤
      ∑ f : Fin m → primeSlabPrimes R, primeSlabWeight R f :=
    sum_le_sum_of_subset_of_nonneg (subset_univ S) (by
      intro f _ _; unfold primeSlabWeight; positivity)
  have hprod : (∑ f : Fin m → primeSlabPrimes R, primeSlabWeight R f) =
      (∑ p ∈ primeSlabPrimes R, 1/(p : ℝ)) ^ m := by
    simpa only [primeSlabWeight, Fintype.card_fin] using primeSlab_product_mass (α := Fin m) R
  rw [hprod] at hsubset
  have hmass := hsubset.trans (pow_le_pow_left₀ (sum_nonneg (fun p _ => by positivity)) hm5 m)
  calc
    _ ≤ (log R * R ^ (-a)) * (∑ f ∈ S, primeSlabWeight R f) := (cap_sum_bound hR S j phi b a hS).2
    _ ≤ (log R * R ^ (-a)) * 5 ^ m := mul_le_mul_of_nonneg_left hmass
      (mul_nonneg (log_pos hR).le (rpow_nonneg (by linarith) _))
    _ = _ := mul_comm _ _

 theorem cap_decay (a : ℝ) (ha : 0 < a) :
    Tendsto (fun R : ℝ => log R * R ^ (-a)) atTop (nhds 0) := by
  have hh := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [rpow_neg hR.le, div_eq_mul_inv]
end SecondFunctionalUnitPrimeFibre

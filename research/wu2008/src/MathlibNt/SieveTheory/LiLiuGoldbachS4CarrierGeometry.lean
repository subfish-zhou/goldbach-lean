import MathlibNt.SieveTheory.LiLiuGoldbachG10Cofactor

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachS4CarrierGeometry (P : Prop) : Decidable P := Classical.propDecidable P

theorem mem_goldbachS4Pairs_iff {N : ℕ} {u : ℝ} {rs : ℕ × ℕ} :
    rs ∈ goldbachS4Pairs N u ↔
      rs.1.Prime ∧ rs.2.Prime ∧ Nat.Coprime (rs.1 * rs.2) N ∧
        u ≤ (rs.1 : ℝ) ∧ rs.1 ≤ rs.2 ∧ rs.1 * rs.2 ^ 2 ≤ N := by
  rw [goldbachS4Pairs, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, h⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        ((Nat.le_mul_of_pos_right rs.1 (pow_pos h.2.1.pos 2)).trans h.2.2.2.2.2))
    · apply Finset.mem_range.mpr
      have hs : rs.2 ≤ rs.2 ^ 2 := by nlinarith [h.2.1.one_le]
      exact Nat.lt_succ_of_le (hs.trans
        ((Nat.le_mul_of_pos_left (rs.2 ^ 2) h.1.pos).trans h.2.2.2.2.2))

def goldbachC8Prod (rs : ℕ × ℕ) : ℕ := rs.1 * rs.2

theorem goldbachC8Prod_pos {N : ℕ} {u : ℝ} {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachS4Pairs N u) : 0 < goldbachC8Prod rs := by
  have h := mem_goldbachS4Pairs_iff.mp hrs
  exact Nat.mul_pos h.1.pos h.2.1.pos

theorem goldbachS4Pair_power_geometry {N : ℕ} {u : ℝ} {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachS4Pairs N u) :
    rs.1 ^ 3 ≤ N ∧ (goldbachC8Prod rs) ^ 2 ≤ rs.1 * N := by
  obtain ⟨_, _, _, _, hle, hprod⟩ := mem_goldbachS4Pairs_iff.mp hrs
  constructor
  · calc
      rs.1 ^ 3 = rs.1 * rs.1 ^ 2 := by ring
      _ ≤ rs.1 * rs.2 ^ 2 := by gcongr
      _ ≤ N := hprod
  · calc
      (goldbachC8Prod rs) ^ 2 = rs.1 * (rs.1 * rs.2 ^ 2) := by
        unfold goldbachC8Prod
        ring
      _ ≤ rs.1 * N := Nat.mul_le_mul_left _ hprod

theorem goldbachC8Prod_le_two_thirds {N : ℕ} {u : ℝ} {rs : ℕ × ℕ}
    (hN : 2 ≤ N) (hrs : rs ∈ goldbachS4Pairs N u) :
    (goldbachC8Prod rs : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hr3, hm2⟩ := goldbachS4Pair_power_geometry hrs
  have hr3R : (rs.1 : ℝ) ^ 3 ≤ N := by exact_mod_cast hr3
  have hr : (rs.1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (rs.1 : ℝ) ^ 3)
      hr3R (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ rs.1)] at h
    norm_num at h
    exact h
  have hm2R : (goldbachC8Prod rs : ℝ) ^ 2 ≤ (rs.1 : ℝ) * N := by
    exact_mod_cast hm2
  have hpow : ((N : ℝ) ^ ((2 : ℝ) / 3)) ^ 2 =
      (N : ℝ) ^ ((1 : ℝ) / 3) * N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (4 : ℝ) / 3 = 1 / 3 + 1 by norm_num,
      Real.rpow_add hN0, Real.rpow_one]
  have hle := hm2R.trans (mul_le_mul_of_nonneg_right hr hN0.le)
  have hnonneg : 0 ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hN0.le _
  nlinarith

theorem goldbachC8Prod_support_bounds {N : ℕ} {rs : ℕ × ℕ}
    (hN : 2 ≤ N) (hrs : rs ∈ goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11))) :
    (N : ℝ) ^ ((6 : ℝ) / 11) ≤ (goldbachC8Prod rs : ℝ) ∧
      (goldbachC8Prod rs : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
  have h := mem_goldbachS4Pairs_iff.mp hrs
  have hs : (N : ℝ) ^ ((3 : ℝ) / 11) ≤ (rs.2 : ℝ) :=
    h.2.2.2.1.trans (by exact_mod_cast h.2.2.2.2.1)
  refine ⟨?_, goldbachC8Prod_le_two_thirds hN hrs⟩
  calc
    (N : ℝ) ^ ((6 : ℝ) / 11) =
        (N : ℝ) ^ ((3 : ℝ) / 11) * (N : ℝ) ^ ((3 : ℝ) / 11) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
      norm_num
    _ ≤ (rs.1 : ℝ) * (rs.2 : ℝ) :=
      mul_le_mul h.2.2.2.1 hs (by positivity) (by positivity)
    _ = (goldbachC8Prod rs : ℝ) := by simp [goldbachC8Prod]

theorem goldbachS4Cutoff_fourth_gt {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) < ((N : ℝ) ^ ((3 : ℝ) / 11)) ^ 4 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
  norm_num only [Nat.cast_ofNat]
  calc
    (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ < (N : ℝ) ^ ((12 : ℝ) / 11) :=
      Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num)

theorem goldbachC8Prod_injOn {N : ℕ} {u : ℝ} :
    Set.InjOn goldbachC8Prod (goldbachS4Pairs N u) := by
  rintro ⟨r, s⟩ hrs ⟨t, v⟩ htv hprod
  have h := mem_goldbachS4Pairs_iff.mp hrs
  have k := mem_goldbachS4Pairs_iff.mp htv
  dsimp only at h k
  change r * s = t * v at hprod
  have hrdvd : r ∣ t * v := hprod ▸ dvd_mul_right r s
  rcases h.1.dvd_mul.mp hrdvd with hrt | hrv
  · have hrt := (Nat.prime_dvd_prime_iff_eq h.1 k.1).mp hrt
    subst t
    have hsv := Nat.mul_left_cancel h.1.pos hprod
    simp [hsv]
  · have hrv := (Nat.prime_dvd_prime_iff_eq h.1 k.2.1).mp hrv
    subst v
    rw [mul_comm t r] at hprod
    have hst := Nat.mul_left_cancel h.1.pos hprod
    have hrs : r = s := le_antisymm h.2.2.2.2.1 (by simpa [hst] using k.2.2.2.2.1)
    simp [hrs, hst]

noncomputable def goldbachC8ProductSupport (N : ℕ) : Finset ℕ :=
  (goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11))).image goldbachC8Prod

noncomputable def goldbachC8ProductFiber (N m : ℕ) : Finset (ℕ × ℕ) :=
  (goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11))).filter fun rs => goldbachC8Prod rs = m

noncomputable def goldbachC8Coeff (N m : ℕ) : ℕ :=
  (goldbachC8ProductFiber N m).card

theorem goldbachC8Coeff_le_one (N m : ℕ) : goldbachC8Coeff N m ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro rs hrs tu htu
  obtain ⟨hrs, hrm⟩ := Finset.mem_filter.mp hrs
  obtain ⟨htu, htm⟩ := Finset.mem_filter.mp htu
  exact goldbachC8Prod_injOn hrs htu (hrm.trans htm.symm)

theorem goldbachC8Coeff_pos_iff {N m : ℕ} :
    0 < goldbachC8Coeff N m ↔ m ∈ goldbachC8ProductSupport N := by
  simp only [goldbachC8Coeff, Finset.card_pos, Finset.Nonempty,
    goldbachC8ProductFiber, Finset.mem_filter, goldbachC8ProductSupport, Finset.mem_image]

theorem goldbachC8ProductSupport_bounds {N m : ℕ}
    (hN : 2 ≤ N) (hm : m ∈ goldbachC8ProductSupport N) :
    (N : ℝ) ^ ((6 : ℝ) / 11) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨rs, hrs, rfl⟩ := Finset.mem_image.mp hm
  exact goldbachC8Prod_support_bounds hN hrs

theorem goldbachS4Pair_mem_largePrimeDivisors {N n : ℕ} {u : ℝ} {rs : ℕ × ℕ}
    (hn : n ≠ 0) (hrs : rs ∈ goldbachS4Pairs N u) (hd : goldbachC8Prod rs ∣ n) :
    rs ∈ (largePrimeDivisors n u).product (largePrimeDivisors n u) := by
  have h := mem_goldbachS4Pairs_iff.mp hrs
  have hr : rs.1 ∣ n := (dvd_mul_right rs.1 rs.2).trans hd
  have hs : rs.2 ∣ n := (dvd_mul_left rs.2 rs.1).trans hd
  have hsu : u ≤ (rs.2 : ℝ) := h.2.2.2.1.trans (by exact_mod_cast h.2.2.2.2.1)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨h.1, hr, hn⟩, h.2.2.2.1⟩,
      Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨h.2.1, hs, hn⟩, hsu⟩⟩

theorem goldbachS4Pair_dvdFiber_card_le_fourHundred {N n : ℕ}
    (hn1 : 1 ≤ n) (hnN : n < N) :
    ((goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11))).filter
      fun rs => goldbachC8Prod rs ∣ n).card ≤ 400 := by
  have hcap := largePrimeDivisors_card_le_twenty hn1 hnN
    (by norm_num : (1 : ℝ) / 21 < 3 / 11)
  have hsub : ((goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11))).filter
      fun rs => goldbachC8Prod rs ∣ n) ⊆
      (largePrimeDivisors n ((N : ℝ) ^ ((3 : ℝ) / 11))).product
        (largePrimeDivisors n ((N : ℝ) ^ ((3 : ℝ) / 11))) := by
    intro rs hrs
    obtain ⟨hrs, hd⟩ := Finset.mem_filter.mp hrs
    exact goldbachS4Pair_mem_largePrimeDivisors (by omega) hrs hd
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ = _ := Finset.card_product _ _
    _ ≤ 20 * 20 := Nat.mul_le_mul hcap hcap
    _ = 400 := by norm_num

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
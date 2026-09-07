import MathlibNt.SieveTheory.LiLiuGoldbachG11SwitchedMother
import MathlibNt.SieveTheory.LiLiuGoldbachG11BodyMinFac
import MathlibNt.SieveTheory.LiLiuGoldbachErrorFoundations

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11SwitchedBodyProd_minFac {N : ℕ} {z b : ℝ}
    {u : GoldbachG11SwitchedBody} (hu : u ∈ goldbachG11SwitchedBodies N z b) :
    (goldbachG11SwitchedBodyProd u).minFac = u.2.2.1 := by
  rcases u with ⟨t, s, q, k⟩
  obtain ⟨hq, hs, ht, _, _, hqs, hst, _, _, _, hk, _⟩ :=
    mem_goldbachG11SwitchedBodies_iff.mp hu
  exact goldbachG11_body_minFac hq hs ht hqs hst hk

noncomputable def goldbachG11ProductSupport (N : ℕ) (z b : ℝ) : Finset ℕ :=
  (goldbachG11GoodSwitchedBodies N z b).image goldbachG11SwitchedBodyProd

noncomputable def goldbachG11ProductFiber (N : ℕ) (z b : ℝ) (m : ℕ) :
    Finset GoldbachG11SwitchedBody := by
  classical
  exact (goldbachG11GoodSwitchedBodies N z b).filter fun u =>
    goldbachG11SwitchedBodyProd u = m

noncomputable def goldbachG11ProductCoefficient (N : ℕ) (z b : ℝ) (m : ℕ) : ℕ :=
  (goldbachG11ProductFiber N z b m).card

theorem mem_goldbachG11ProductSupport_iff {N m : ℕ} {z b : ℝ} :
    m ∈ goldbachG11ProductSupport N z b ↔
      ∃ u ∈ goldbachG11GoodSwitchedBodies N z b, goldbachG11SwitchedBodyProd u = m := by
  classical
  exact Finset.mem_image

theorem mem_goldbachG11ProductFiber_iff {N m : ℕ} {z b : ℝ}
    {u : GoldbachG11SwitchedBody} :
    u ∈ goldbachG11ProductFiber N z b m ↔
      u ∈ goldbachG11GoodSwitchedBodies N z b ∧ goldbachG11SwitchedBodyProd u = m := by
  classical
  exact Finset.mem_filter

theorem goldbachG11ProductSupport_data {N m : ℕ} {z b : ℝ}
    (hm : m ∈ goldbachG11ProductSupport N z b) :
    0 < m ∧ m < N ∧ Nat.Coprime m N ∧ z ≤ (m.minFac : ℝ) := by
  obtain ⟨u, hu, rfl⟩ := mem_goldbachG11ProductSupport_iff.mp hm
  obtain ⟨hu, hcop⟩ := mem_goldbachG11GoodSwitchedBodies_iff.mp hu
  refine ⟨goldbachG11SwitchedBodyProd_pos hu, ?_, hcop, ?_⟩
  · rcases u with ⟨t, s, q, k⟩
    exact (mem_goldbachG11SwitchedBodies_iff.mp hu).2.2.2.2.2.2.2.2.2.2.2
  · rw [goldbachG11SwitchedBodyProd_minFac hu]
    rcases u with ⟨t, s, q, k⟩
    exact (mem_goldbachG11SwitchedBodies_iff.mp hu).2.2.2.2.1

theorem goldbachG11ProductFiber_nonempty_iff {N m : ℕ} {z b : ℝ} :
    (goldbachG11ProductFiber N z b m).Nonempty ↔
      m ∈ goldbachG11ProductSupport N z b := by
  classical
  simp only [Finset.nonempty_def, mem_goldbachG11ProductFiber_iff,
    mem_goldbachG11ProductSupport_iff]

theorem goldbachG11ProductCoefficient_pos_iff {N m : ℕ} {z b : ℝ} :
    0 < goldbachG11ProductCoefficient N z b m ↔
      m ∈ goldbachG11ProductSupport N z b := by
  exact Finset.card_pos.trans goldbachG11ProductFiber_nonempty_iff

theorem goldbachG11ProductCoefficient_eq_zero_iff {N m : ℕ} {z b : ℝ} :
    goldbachG11ProductCoefficient N z b m = 0 ↔
      m ∉ goldbachG11ProductSupport N z b := by
  rw [← goldbachG11ProductCoefficient_pos_iff]
  omega

theorem goldbachG11ProductCoefficient_eq_zero_of_not_mem {N m : ℕ} {z b : ℝ}
    (hm : m ∉ goldbachG11ProductSupport N z b) :
    goldbachG11ProductCoefficient N z b m = 0 :=
  goldbachG11ProductCoefficient_eq_zero_iff.mpr hm

def goldbachG11ProductCoordinates (u : GoldbachG11SwitchedBody) : ℕ × ℕ :=
  (u.2.1, u.1)

-- Only a fixed-product fiber is injective in these two coordinates.
theorem goldbachG11ProductCoordinates_injOn (N m : ℕ) (z b : ℝ) :
    Set.InjOn goldbachG11ProductCoordinates (goldbachG11ProductFiber N z b m) := by
  rintro ⟨t, s, q, k⟩ hu ⟨t', s', q', k'⟩ hv heq
  obtain ⟨hu, hmu⟩ := mem_goldbachG11ProductFiber_iff.mp hu
  obtain ⟨hv, hmv⟩ := mem_goldbachG11ProductFiber_iff.mp hv
  have huB := (mem_goldbachG11GoodSwitchedBodies_iff.mp hu).1
  have hvB := (mem_goldbachG11GoodSwitchedBodies_iff.mp hv).1
  have hqu : m.minFac = q := hmu ▸ goldbachG11SwitchedBodyProd_minFac huB
  have hqv : m.minFac = q' := hmv ▸ goldbachG11SwitchedBodyProd_minFac hvB
  have hqq : q = q' := hqu.symm.trans hqv
  have hst : s = s' ∧ t = t' := by
    simpa only [goldbachG11ProductCoordinates, Prod.mk.injEq] using heq
  rcases hst with ⟨rfl, rfl⟩
  clear hqu hqv
  rcases hqq with rfl
  obtain ⟨hq, hs, ht, _⟩ := mem_goldbachG11SwitchedBodies_iff.mp huB
  have hpos : 0 < q * s * t := mul_pos (mul_pos hq.pos hs.pos) ht.pos
  have hprod : q * s * t * k = q * s * t * k' := hmu.trans hmv.symm
  have hkk : k = k' := mul_left_cancel₀ (ne_of_gt hpos) hprod
  subst k'
  rfl

theorem goldbachG11ProductCoordinates_mem_largePrimeDivisors
    {N m : ℕ} {z b : ℝ} {u : GoldbachG11SwitchedBody}
    (hu : u ∈ goldbachG11ProductFiber N z b m) :
    goldbachG11ProductCoordinates u ∈
      (largePrimeDivisors m z).product (largePrimeDivisors m z) := by
  obtain ⟨hu, heq⟩ := mem_goldbachG11ProductFiber_iff.mp hu
  have huB := (mem_goldbachG11GoodSwitchedBodies_iff.mp hu).1
  have hm0 : m ≠ 0 := ne_of_gt (heq ▸ goldbachG11SwitchedBodyProd_pos huB)
  rcases u with ⟨t, s, q, k⟩
  obtain ⟨_, hs, ht, _, hzq, hqs, hst, _⟩ :=
    mem_goldbachG11SwitchedBodies_iff.mp huB
  have hsm : s ∣ m := heq ▸
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left s q) t) k
  have htm : t ∣ m := heq ▸ dvd_mul_of_dvd_left (dvd_mul_left t (q * s)) k
  have hzs : z ≤ (s : ℝ) := hzq.trans (by exact_mod_cast hqs)
  have hzt : z ≤ (t : ℝ) := hzs.trans (by exact_mod_cast hst)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hs, hsm, hm0⟩, hzs⟩,
      Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨ht, htm, hm0⟩, hzt⟩⟩

theorem goldbachG11ProductCoefficient_le_four_hundred (N m : ℕ) :
    goldbachG11ProductCoefficient N ((N : ℝ) ^ ((4 : ℝ) / 53))
      ((N : ℝ) ^ ((4 : ℝ) / 33)) m ≤ 400 := by
  classical
  let z : ℝ := (N : ℝ) ^ ((4 : ℝ) / 53)
  let b : ℝ := (N : ℝ) ^ ((4 : ℝ) / 33)
  change (goldbachG11ProductFiber N z b m).card ≤ 400
  by_cases hne : (goldbachG11ProductFiber N z b m).Nonempty
  · have hm := goldbachG11ProductSupport_data
      (goldbachG11ProductFiber_nonempty_iff.mp hne)
    have hn1 : 1 ≤ m := hm.1
    have hnN : m < N := hm.2.1
    let L := largePrimeDivisors m z
    have hcap : L.card ≤ 20 := largePrimeDivisors_card_le_twenty hn1 hnN
      (by norm_num : (1 : ℝ) / 21 < 4 / 53)
    have hcard : (goldbachG11ProductFiber N z b m).card ≤ (L.product L).card :=
      Finset.card_le_card_of_injOn goldbachG11ProductCoordinates
        (fun _ hu => goldbachG11ProductCoordinates_mem_largePrimeDivisors hu)
        (goldbachG11ProductCoordinates_injOn N m z b)
    calc
      (goldbachG11ProductFiber N z b m).card ≤ (L.product L).card := hcard
      _ = L.card * L.card := Finset.card_product _ _
      _ = L.card ^ 2 := (pow_two _).symm
      _ ≤ 20 ^ 2 := Nat.pow_le_pow_left hcap 2
      _ = 400 := by norm_num
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    norm_num

noncomputable def goldbachG11NormalizedProductCoefficient
    (N : ℕ) (z b : ℝ) (m : ℕ) : ℝ :=
  (goldbachG11ProductCoefficient N z b m : ℝ) / 400

theorem goldbachG11NormalizedProductCoefficient_nonneg (N m : ℕ) (z b : ℝ) :
    0 ≤ goldbachG11NormalizedProductCoefficient N z b m := by
  unfold goldbachG11NormalizedProductCoefficient
  positivity

theorem goldbachG11NormalizedProductCoefficient_le_one (N m : ℕ) :
    goldbachG11NormalizedProductCoefficient N ((N : ℝ) ^ ((4 : ℝ) / 53))
      ((N : ℝ) ^ ((4 : ℝ) / 33)) m ≤ 1 := by
  have h : (goldbachG11ProductCoefficient N ((N : ℝ) ^ ((4 : ℝ) / 53))
      ((N : ℝ) ^ ((4 : ℝ) / 33)) m : ℝ) ≤ 400 := by
    exact_mod_cast goldbachG11ProductCoefficient_le_four_hundred N m
  unfold goldbachG11NormalizedProductCoefficient
  linarith

theorem goldbachG11NormalizedProductCoefficient_mul_four_hundred
    (N m : ℕ) (z b : ℝ) :
    400 * goldbachG11NormalizedProductCoefficient N z b m =
      (goldbachG11ProductCoefficient N z b m : ℝ) := by
  unfold goldbachG11NormalizedProductCoefficient
  ring

theorem goldbachG11NormalizedProductCoefficient_eq_zero_of_not_mem
    {N m : ℕ} {z b : ℝ} (hm : m ∉ goldbachG11ProductSupport N z b) :
    goldbachG11NormalizedProductCoefficient N z b m = 0 := by
  simp [goldbachG11NormalizedProductCoefficient,
    goldbachG11ProductCoefficient_eq_zero_of_not_mem hm]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
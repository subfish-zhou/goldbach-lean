import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernel
import MathlibNt.SieveTheory.PrimeReciprocalLogRectangle

open Finset Filter Set
open scoped BigOperators Topology

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open PrimeReciprocalLogScale PrimeReciprocalLogRectangle

def goldbachG11PrimeInterval (N : ℕ) (a b : ℝ) : Finset ℕ :=
  (Finset.range (rpowFloor N b + 1)).filter
    (fun p => p.Prime ∧ (N : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) ^ b)

theorem mem_goldbachG11PrimeInterval {N p : ℕ} {a b : ℝ} :
    p ∈ goldbachG11PrimeInterval N a b ↔
      p.Prime ∧ (N : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) ^ b := by
  classical
  simp only [goldbachG11PrimeInterval, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun hp => hp.2
  · intro hp
    exact ⟨Nat.lt_succ_iff.mpr (Nat.le_floor hp.2.2), hp⟩

/-- Coordinates 0,1,2,3 are r,q,s,t; the carrier keeps the production sigma order. -/
def goldbachG11PrimeBox (N : ℕ) (lo hi : Fin 4 → ℝ) : Finset GoldbachG11Label :=
  (goldbachG11PrimeInterval N (lo 3) (hi 3)).sigma fun _t =>
    (goldbachG11PrimeInterval N (lo 2) (hi 2)).sigma fun _s =>
      (goldbachG11PrimeInterval N (lo 0) (hi 0)).sigma fun _r =>
        goldbachG11PrimeInterval N (lo 1) (hi 1)

def goldbachG11PrimeBoxMass (N : ℕ) (lo hi : Fin 4 → ℝ) : ℝ :=
  ∑ v ∈ goldbachG11PrimeBox N lo hi, 1 / (goldbachG11LabelProd v : ℝ)

def goldbachG11LogBoxMass (lo hi : Fin 4 → ℝ) : ℝ :=
  logarithmicRectangleMass (lo 0) (hi 0) (lo 1) (hi 1) *
    logarithmicRectangleMass (lo 2) (hi 2) (lo 3) (hi 3)

theorem goldbachG11PrimeBoxMass_eq_rectangles (N : ℕ) (lo hi : Fin 4 → ℝ) :
    goldbachG11PrimeBoxMass N lo hi =
      primeReciprocalLogRectangle N (lo 0) (hi 0) (lo 1) (hi 1) *
        primeReciprocalLogRectangle N (lo 2) (hi 2) (lo 3) (hi 3) := by
  simp only [goldbachG11PrimeBoxMass, goldbachG11PrimeBox, Finset.sum_sigma,
    goldbachG11LabelProd, Nat.cast_mul, one_div, mul_inv]
  rw [primeReciprocalLogRectangle_eq_mul, primeReciprocalLogRectangle_eq_mul]
  change (∑ t ∈ goldbachG11PrimeInterval N (lo 3) (hi 3),
    ∑ s ∈ goldbachG11PrimeInterval N (lo 2) (hi 2),
      ∑ r ∈ goldbachG11PrimeInterval N (lo 0) (hi 0),
        ∑ q ∈ goldbachG11PrimeInterval N (lo 1) (hi 1),
          (r : ℝ)⁻¹ * (q : ℝ)⁻¹ * (s : ℝ)⁻¹ * (t : ℝ)⁻¹) = _
  simp only [← Finset.sum_mul, ← Finset.mul_sum, primeReciprocalLogInterval,
    goldbachG11PrimeInterval, one_div]
  ring

theorem tendsto_goldbachG11PrimeBoxMass (lo hi : Fin 4 → ℝ)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, lo i < hi i) :
    Tendsto (fun N : ℕ => goldbachG11PrimeBoxMass N lo hi) atTop
      (nhds (goldbachG11LogBoxMass lo hi)) := by
  simpa only [goldbachG11PrimeBoxMass_eq_rectangles, goldbachG11LogBoxMass] using
    (tendsto_primeReciprocalLogRectangle (hlo 0) (hhi 0) (hlo 1) (hhi 1)).mul
      (tendsto_primeReciprocalLogRectangle (hlo 2) (hhi 2) (hlo 3) (hhi 3))

theorem tendsto_goldbachG11PrimeBoxMass_sum {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) (lo hi : ι → Fin 4 → ℝ)
    (hlo : ∀ j ∈ S, ∀ i, 0 < lo j i) (hhi : ∀ j ∈ S, ∀ i, lo j i < hi j i) :
    Tendsto (fun N : ℕ => ∑ j ∈ S, c j * goldbachG11PrimeBoxMass N (lo j) (hi j))
      atTop (nhds (∑ j ∈ S, c j * goldbachG11LogBoxMass (lo j) (hi j))) := by
  apply tendsto_finsetSum
  intro j hj
  exact (tendsto_goldbachG11PrimeBoxMass (lo j) (hi j) (hlo j hj) (hhi j hj)).const_mul _

/-- The strict lower endpoint is justified by the prime-cutoff theorem, not discarded. -/
theorem goldbachG11Labels_subset_primeBox (N : ℕ) :
    goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) ⊆
      goldbachG11PrimeBox N (fun _ => 4 / 53) (fun _ => 4 / 33) := by
  rintro ⟨t, s, r, q⟩ hv
  obtain ⟨hr, hq, hs, ht, _, hl, hrq, hqs, hst, hu⟩ :=
    mem_goldbachG11Labels_iff.mp hv
  have hrqR : (r : ℝ) ≤ q := by exact_mod_cast hrq
  have hqsR : (q : ℝ) ≤ s := by exact_mod_cast hqs
  have hstR : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hrl := (goldbachG11_prime_lower_cutoff_iff N r hr).mp hl
  simp only [goldbachG11PrimeBox, Finset.mem_sigma, mem_goldbachG11PrimeInterval]
  exact ⟨⟨ht, ((hrl.trans_le hrqR).trans_le hqsR).trans_le hstR, hu⟩,
    ⟨hs, (hrl.trans_le hrqR).trans_le hqsR, hstR.trans hu⟩,
    ⟨hr, hrl, hrqR.trans (hqsR.trans (hstR.trans hu))⟩,
    hq, hrl.trans_le hrqR, hqsR.trans (hstR.trans hu)⟩

def goldbachG11OrderedPrimeLabels (N : ℕ) : Finset GoldbachG11Label :=
  (goldbachG11PrimeBox N (fun _ => 4 / 53) (fun _ => 4 / 33)).filter
    (fun v => v.2.2.1 ≤ v.2.2.2 ∧ v.2.2.2 ≤ v.2.1 ∧ v.2.1 ≤ v.1)


def goldbachG11PrimeBoxContribution (h : ℝ → ℝ) (N : ℕ) (lo hi : Fin 4 → ℝ) : ℝ :=
  ∑ v ∈ (goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ))).filter (fun v => v ∈ goldbachG11PrimeBox N lo hi),
    h (Real.log (v.2.2.1 : ℝ) / Real.log (N : ℝ)) * Real.log (N : ℝ) /
      ((goldbachG11LabelProd v : ℝ) * Real.log (v.2.2.2 : ℝ))

theorem goldbachG11PrimeBoxContribution_le (h : ℝ → ℝ) {N : ℕ} (hN : 4 ≤ N)
    (lo hi : Fin 4 → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r ∈ Ioc (lo 0) (hi 0), ∀ q ∈ Ioc (lo 1) (hi 1), h r / q ≤ C) :
    goldbachG11PrimeBoxContribution h N lo hi ≤ C * goldbachG11PrimeBoxMass N lo hi := by
  classical
  unfold goldbachG11PrimeBoxContribution goldbachG11PrimeBoxMass
  calc
    _ ≤ ∑ v ∈ (goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (4 / 33 : ℝ))).filter (fun v => v ∈ goldbachG11PrimeBox N lo hi),
          C * (1 / (goldbachG11LabelProd v : ℝ)) := by
      apply Finset.sum_le_sum
      rintro ⟨t, s, r, q⟩ hv
      obtain ⟨_, hp⟩ := Finset.mem_filter.mp hv
      simp only [goldbachG11PrimeBox, Finset.mem_sigma, mem_goldbachG11PrimeInterval] at hp
      have hr := (LiuWeight.primeLogExponent_mem_interval_iff (by omega : 1 < N)
        hp.2.2.1.1.pos (lo 0) (hi 0)).mpr hp.2.2.1.2
      have hq := (LiuWeight.primeLogExponent_mem_interval_iff (by omega : 1 < N)
        hp.2.2.2.1.pos (lo 1) (hi 1)).mpr hp.2.2.2.2
      have he :
          h (Real.log (r : ℝ) / Real.log (N : ℝ)) * Real.log (N : ℝ) /
            ((goldbachG11LabelProd ⟨t, s, r, q⟩ : ℝ) * Real.log (q : ℝ)) =
          (h (Real.log (r : ℝ) / Real.log (N : ℝ)) /
            (Real.log (q : ℝ) / Real.log (N : ℝ))) *
              (1 / (goldbachG11LabelProd ⟨t, s, r, q⟩ : ℝ)) := by
        simp only [div_eq_mul_inv, mul_inv, inv_inv]
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (hbound _ hr _ hq) (by positivity)
    _ ≤ ∑ v ∈ goldbachG11PrimeBox N lo hi, C * (1 / (goldbachG11LabelProd v : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (fun v hv => (Finset.mem_filter.mp hv).2)
      intro v _ _
      exact mul_nonneg hC (by positivity)
    _ = _ := by rw [Finset.mul_sum]

/-- Finite covers may overlap. This is not an assumption about a prime-to-integral limit. -/
theorem goldbachG11PrimeKernel_le_boxCover {ι : Type*} (S : Finset ι)
    (h : ℝ → ℝ) (hh : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    {N : ℕ} (hN : 4 ≤ N) (lo hi : ι → Fin 4 → ℝ) (C : ι → ℝ)
    (hC : ∀ j ∈ S, 0 ≤ C j)
    (hbound : ∀ j ∈ S, ∀ r ∈ Ioc (lo j 0) (hi j 0),
      ∀ q ∈ Ioc (lo j 1) (hi j 1), h r / q ≤ C j)
    (hcover : ∀ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ)), ∃ j ∈ S, v ∈ goldbachG11PrimeBox N (lo j) (hi j)) :
    goldbachG11PrimeKernel h N ≤
      ∑ j ∈ S, C j * goldbachG11PrimeBoxMass N (lo j) (hi j) := by
  classical
  let f : GoldbachG11Label → ℝ := fun v =>
    h (Real.log (v.2.2.1 : ℝ) / Real.log (N : ℝ)) * Real.log (N : ℝ) /
      ((goldbachG11LabelProd v : ℝ) * Real.log (v.2.2.2 : ℝ))
  have hf : ∀ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ)), 0 ≤ f v := by
    intro v hv
    have hg := goldbachG11PrimeKernel_logGeometry hN hv
    exact div_nonneg (mul_nonneg (hh _ hg.1)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))))
      (mul_nonneg (Nat.cast_nonneg _) hg.2.1.le)
  calc
    _ ≤ ∑ j ∈ S, goldbachG11PrimeBoxContribution h N (lo j) (hi j) := by
      change (∑ v ∈ goldbachG11Labels N _ _, f v) ≤ _
      unfold goldbachG11PrimeBoxContribution
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨j, hj, hvj⟩ := hcover v hv
      change f v ≤ ∑ j ∈ S, if v ∈ goldbachG11PrimeBox N (lo j) (hi j) then f v else 0
      calc
        _ = if v ∈ goldbachG11PrimeBox N (lo j) (hi j) then f v else 0 := by rw [if_pos hvj]
        _ ≤ _ := Finset.single_le_sum
          (f := fun k : ι => if v ∈ goldbachG11PrimeBox N (lo k) (hi k) then f v else 0)
          (fun _ _ => ite_nonneg (hf v hv) le_rfl) hj
    _ ≤ _ := Finset.sum_le_sum (fun j hj =>
      goldbachG11PrimeBoxContribution_le h hN (lo j) (hi j) (C j) (hC j hj) (hbound j hj))

theorem goldbachG11PrimeKernel_le_fixedCover_eventually {ι : Type*} (S : Finset ι)
    (h : ℝ → ℝ) (hh : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    (lo hi : ι → Fin 4 → ℝ) (C : ι → ℝ)
    (hlo : ∀ j ∈ S, ∀ i, 0 < lo j i) (hhi : ∀ j ∈ S, ∀ i, lo j i < hi j i)
    (hC : ∀ j ∈ S, 0 ≤ C j)
    (hbound : ∀ j ∈ S, ∀ r ∈ Ioc (lo j 0) (hi j 0),
      ∀ q ∈ Ioc (lo j 1) (hi j 1), h r / q ≤ C j)
    (hcover : ∀ N : ℕ, 4 ≤ N → ∀ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ)), ∃ j ∈ S, v ∈ goldbachG11PrimeBox N (lo j) (hi j))
    (ν : ℝ) (hν : 0 < ν) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG11PrimeKernel h N ≤
        (∑ j ∈ S, C j * goldbachG11LogBoxMass (lo j) (hi j)) + ν := by
  have hc := (Metric.tendsto_nhds.mp
    (tendsto_goldbachG11PrimeBoxMass_sum S C lo hi hlo hhi)) ν hν
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hc
  refine ⟨max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have he := hN₁ N ((le_max_right _ _).trans hN)
  rw [Real.dist_eq] at he
  exact (goldbachG11PrimeKernel_le_boxCover S h hh hN4 lo hi C hC hbound
    (hcover N hN4)).trans (by linarith [(abs_lt.mp he).2])


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
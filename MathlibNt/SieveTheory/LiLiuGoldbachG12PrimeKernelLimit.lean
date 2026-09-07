import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernel
import MathlibNt.SieveTheory.PrimeReciprocalLogRectangle

open Finset Filter Set
open scoped BigOperators Topology

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open PrimeReciprocalLogScale PrimeReciprocalLogRectangle

theorem goldbachG12PrimeKernel_eq_logCoordinateSum (h : ℝ → ℝ) (N : ℕ) :
    goldbachG12PrimeKernel h N =
      ∑ v ∈ goldbachG12Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ)),
        (h (Real.log (v.2.2.1 : ℝ) / Real.log (N : ℝ)) /
          (Real.log (v.2.2.2 : ℝ) / Real.log (N : ℝ))) *
            (1 / (goldbachG11LabelProd v : ℝ)) := by
  apply Finset.sum_congr rfl
  intro v _
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

def goldbachG12PrimeBoxContribution (h : ℝ → ℝ) (N : ℕ) (lo hi : Fin 4 → ℝ) : ℝ :=
  ∑ v ∈ (goldbachG12Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ))).filter (fun v => v ∈ goldbachG11PrimeBox N lo hi),
    h (Real.log (v.2.2.1 : ℝ) / Real.log (N : ℝ)) * Real.log (N : ℝ) /
      ((goldbachG11LabelProd v : ℝ) * Real.log (v.2.2.2 : ℝ))

theorem goldbachG12PrimeBoxContribution_le (h : ℝ → ℝ) {N : ℕ} (hN : 4 ≤ N)
    (lo hi : Fin 4 → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r ∈ Ioc (lo 0) (hi 0), ∀ q ∈ Ioc (lo 1) (hi 1), h r / q ≤ C) :
    goldbachG12PrimeBoxContribution h N lo hi ≤ C * goldbachG11PrimeBoxMass N lo hi := by
  classical
  unfold goldbachG12PrimeBoxContribution goldbachG11PrimeBoxMass
  calc
    _ ≤ ∑ v ∈ (goldbachG12Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (4 / 33 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ))).filter (fun v => v ∈ goldbachG11PrimeBox N lo hi),
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
theorem goldbachG12PrimeKernel_le_boxCover {ι : Type*} (S : Finset ι)
    (h : ℝ → ℝ) (hh : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    {N : ℕ} (hN : 4 ≤ N) (lo hi : ι → Fin 4 → ℝ) (C : ι → ℝ)
    (hC : ∀ j ∈ S, 0 ≤ C j)
    (hbound : ∀ j ∈ S, ∀ r ∈ Ioc (lo j 0) (hi j 0),
      ∀ q ∈ Ioc (lo j 1) (hi j 1), h r / q ≤ C j)
    (hcover : ∀ v ∈ goldbachG12Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ)), ∃ j ∈ S, v ∈ goldbachG11PrimeBox N (lo j) (hi j)) :
    goldbachG12PrimeKernel h N ≤
      ∑ j ∈ S, C j * goldbachG11PrimeBoxMass N (lo j) (hi j) := by
  classical
  let f : GoldbachG11Label → ℝ := fun v =>
    h (Real.log (v.2.2.1 : ℝ) / Real.log (N : ℝ)) * Real.log (N : ℝ) /
      ((goldbachG11LabelProd v : ℝ) * Real.log (v.2.2.2 : ℝ))
  have hf : ∀ v ∈ goldbachG12Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ)), 0 ≤ f v := by
    intro v hv
    have hg := goldbachG12PrimeKernel_logGeometry hN hv
    exact div_nonneg (mul_nonneg (hh _ hg.1)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))))
      (mul_nonneg (Nat.cast_nonneg _) hg.2.le)
  calc
    _ ≤ ∑ j ∈ S, goldbachG12PrimeBoxContribution h N (lo j) (hi j) := by
      change (∑ v ∈ goldbachG12Labels N _ _ _, f v) ≤ _
      unfold goldbachG12PrimeBoxContribution
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
      goldbachG12PrimeBoxContribution_le h hN (lo j) (hi j) (C j) (hC j hj) (hbound j hj))

theorem goldbachG12PrimeKernel_le_fixedCover_eventually {ι : Type*} (S : Finset ι)
    (h : ℝ → ℝ) (hh : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    (lo hi : ι → Fin 4 → ℝ) (C : ι → ℝ)
    (hlo : ∀ j ∈ S, ∀ i, 0 < lo j i) (hhi : ∀ j ∈ S, ∀ i, lo j i < hi j i)
    (hC : ∀ j ∈ S, 0 ≤ C j)
    (hbound : ∀ j ∈ S, ∀ r ∈ Ioc (lo j 0) (hi j 0),
      ∀ q ∈ Ioc (lo j 1) (hi j 1), h r / q ≤ C j)
    (hcover : ∀ N : ℕ, 4 ≤ N → ∀ v ∈ goldbachG12Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ)), ∃ j ∈ S, v ∈ goldbachG11PrimeBox N (lo j) (hi j))
    (ν : ℝ) (hν : 0 < ν) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG12PrimeKernel h N ≤
        (∑ j ∈ S, C j * goldbachG11LogBoxMass (lo j) (hi j)) + ν := by
  have hc := (Metric.tendsto_nhds.mp
    (tendsto_goldbachG11PrimeBoxMass_sum S C lo hi hlo hhi)) ν hν
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hc
  refine ⟨max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have he := hN₁ N ((le_max_right _ _).trans hN)
  rw [Real.dist_eq] at he
  exact (goldbachG12PrimeKernel_le_boxCover S h hh hN4 lo hi C hC hbound
    (hcover N hN4)).trans (by linarith [(abs_lt.mp he).2])


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

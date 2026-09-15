import MathlibNt.Wu2004MeanValue.LiMass
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The tail mass and the continuous-test Mertens sum

The fixed factor `c` in the actual source cutoff is retained. An eventual
power sandwich enlarges that carrier to an exact real-power prime interval.
Only the positive lower li term and the coprimality filter are discarded.
-/

namespace Wu2004MeanValue

open Filter Finset
open MathlibNt.SieveTheory.MertensTheorem
open scoped Topology
noncomputable section

def tailPrimeModel (N : ℕ) (α : ℝ) : ℝ :=
  weightedPrimeReciprocalLogSum (fun u => 1 / (1 - u)) N α (1 / 2)

def tailIntegral (α : ℝ) : ℝ :=
  ∫ u in α..(1 / 2 : ℝ), 1 / (u * (1 - u))

theorem tail_log_scale_le_half {N m : ℕ} (hN : 1 < (N : ℝ))
    (hm : 0 < m) (hms : (m : ℝ) ≤ Real.sqrt N) :
    Real.log m / Real.log N ≤ 1 / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog := Real.log_le_log hm0 hms
  rw [Real.log_sqrt (Nat.cast_nonneg N)] at hlog
  exact (div_le_iff₀ (Real.log_pos hN)).mpr (by linarith)

theorem tail_proxy_eq_model_term {N m : ℕ} (hN : 1 < (N : ℝ))
    (hm : 0 < m) (hms : (m : ℝ) ≤ Real.sqrt N) :
    ((N : ℝ) / m) / Real.log ((N : ℝ) / m) =
      ((N : ℝ) / Real.log N) * ((1 / (1 - Real.log m / Real.log N)) / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : 0 < (N : ℝ) := by linarith
  have hl0 : 0 < Real.log (N : ℝ) := Real.log_pos hN
  have hs := tail_log_scale_le_half hN hm hms
  have hd : 1 - Real.log m / Real.log N ≠ 0 := by linarith
  have hdiff : Real.log (N : ℝ) - Real.log m ≠ 0 := by
    have ht := (div_le_iff₀ hl0).mp hs
    linarith
  rw [Real.log_div hn0.ne' hm0.ne']
  field_simp

theorem tailPrimeModel_nonneg {N : ℕ} (α : ℝ) (hN : 1 < (N : ℝ)) :
    0 ≤ tailPrimeModel N α := by
  unfold tailPrimeModel weightedPrimeReciprocalLogSum
  apply sum_nonneg
  intro m hm
  obtain ⟨hmI, hmp⟩ := mem_filter.mp hm
  have hms : (m : ℝ) ≤ Real.sqrt N := by
    simpa only [Real.sqrt_eq_rpow] using (mem_Ioc_rpowFloor_iff.mp hmI).2
  have hs := tail_log_scale_le_half hN hmp.pos hms
  exact div_nonneg (one_div_nonneg.mpr (by linarith)) (Nat.cast_nonneg m)

theorem tendsto_tailPrimeModel {α : ℝ} (hα : 0 < α) (hαh : α < 1 / 2) :
    Tendsto (fun N : ℕ => tailPrimeModel N α) atTop (nhds (tailIntegral α)) := by
  have hc : ContinuousOn (fun u : ℝ => 1 / (1 - u)) (Set.Icc α (1 / 2)) :=
    continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      (fun u hu => by linarith [hu.2])
  have h := tendsto_weightedPrimeReciprocalLogSum hα hαh hc
  have heq : (fun u : ℝ => (1 / (1 - u)) / u) =
      (fun u : ℝ => 1 / (u * (1 - u))) := by
    funext u
    rw [div_div, mul_comm]
  simpa only [tailPrimeModel, tailIntegral, heq] using h

/-- A fixed positive cutoff factor is absorbed by any strictly smaller
power, not by identifying `c*N^tau` with `N^tau`. -/
theorem eventually_power_le_tail_cutoff (c α τ : ℝ) (hc : 0 < c) (hατ : α < τ) :
    ∀ᶠ x : ℝ in atTop, x ^ α ≤ c * x ^ τ := by
  have hg : ∀ᶠ x : ℝ in atTop, 1 / c ≤ x ^ (τ - α) :=
    (tendsto_rpow_atTop (sub_pos.mpr hατ)).eventually (eventually_ge_atTop _)
  filter_upwards [hg, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hp : 1 ≤ c * x ^ (τ - α) := by
    have := (div_le_iff₀ hc).mp hx
    nlinarith
  have he : x ^ τ = x ^ α * x ^ (τ - α) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hx0.le α)]

/-- Finite carrier comparison. The sole analytic input here is a pointwise
li estimate; the next theorem constructs it uniformly from the frozen
real-endpoint remainder. -/
theorem tailMass_le_model {N : ℕ} {c τ η α δ : ℝ}
    (hN : 1 < (N : ℝ)) (hη : 0 < η) (hη1 : η ≤ 1)
    (hdom : (2 / η) ^ 2 ≤ (N : ℝ)) (hδ : 0 ≤ δ)
    (hcut : (N : ℝ) ^ α ≤ c * (N : ℝ) ^ τ)
    (hli : ∀ t : ℝ, Real.sqrt N ≤ t →
      wuLi t ≤ (1 + δ) * (t / Real.log t)) :
    tailMass N c τ η ≤ (1 + δ) * ((N : ℝ) / Real.log N) * tailPrimeModel N α := by
  classical
  let S := (Ioc (rpowFloor N α) (rpowFloor N (1 / 2))).filter Nat.Prime
  let f := fun m : ℕ => (1 / (1 - Real.log m / Real.log N)) / m
  have hsub : tailSource N c τ ⊆ S := by
    intro m hm
    have hs := mem_tailSource.mp hm
    apply mem_filter.mpr
    refine ⟨mem_Ioc_rpowFloor_iff.mpr ⟨hcut.trans_lt hs.2.2.1, ?_⟩, hs.1⟩
    simpa only [Real.sqrt_eq_rpow] using hs.2.2.2
  have hf : ∀ m ∈ S, 0 ≤ f m := by
    intro m hm
    obtain ⟨hmI, hmp⟩ := mem_filter.mp hm
    have hms : (m : ℝ) ≤ Real.sqrt N := by
      simpa only [Real.sqrt_eq_rpow] using (mem_Ioc_rpowFloor_iff.mp hmI).2
    have hs := tail_log_scale_le_half hN hmp.pos hms
    exact div_nonneg (one_div_nonneg.mpr (by linarith)) (Nat.cast_nonneg m)
  have hscale : 0 ≤ (1 + δ) * ((N : ℝ) / Real.log N) :=
    mul_nonneg (by linarith) (div_nonneg (Nat.cast_nonneg N) (Real.log_pos hN).le)
  calc
    tailMass N c τ η ≤ ∑ m ∈ tailSource N c τ,
        (1 + δ) * ((N : ℝ) / Real.log N) * f m := by
      unfold tailMass intervalMass
      apply sum_le_sum
      intro m hm
      have hs := mem_tailSource.mp hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hs.1.pos
      have hd := tail_prime_endpoint_domain N η hη hη1 hdom m hs.1.pos hs.2.2.2
      have hsqrt : Real.sqrt N ≤ (N : ℝ) / m := by
        apply (le_div_iff₀ hm0).mpr
        have hh := mul_le_mul_of_nonneg_left hs.2.2.2 (Real.sqrt_nonneg (N : ℝ))
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
      calc
        wuLi ((N : ℝ) / m) - wuLi (η * N / m) ≤ wuLi ((N : ℝ) / m) :=
          sub_le_self _ (wuLi_nonneg hd.1)
        _ ≤ (1 + δ) * (((N : ℝ) / m) / Real.log ((N : ℝ) / m)) :=
          hli _ hsqrt
        _ = (1 + δ) * ((N : ℝ) / Real.log N) * f m := by
          rw [tail_proxy_eq_model_term hN hs.1.pos hs.2.2.2]
          exact (mul_assoc _ _ _).symm
    _ ≤ ∑ m ∈ S, (1 + δ) * ((N : ℝ) / Real.log N) * f m :=
      sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => mul_nonneg hscale (hf m hm))
    _ = (1 + δ) * ((N : ℝ) / Real.log N) * tailPrimeModel N α := by
      rw [← mul_sum]
      rfl

theorem eventually_tailMass_le_model (c τ η α δ : ℝ)
    (hc : 0 < c) (hη : 0 < η) (hη1 : η ≤ 1)
    (hατ : α < τ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      tailMass N c τ η ≤ (1 + δ) * ((N : ℝ) / Real.log N) * tailPrimeModel N α := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_wuLi_le_one_add_mul δ hδ)
  have hs : ∀ᶠ N : ℕ in atTop, T ≤ Real.sqrt (N : ℝ) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  have hd : ∀ᶠ N : ℕ in atTop, (2 / η) ^ 2 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hc' := tendsto_natCast_atTop_atTop.eventually
    (eventually_power_le_tail_cutoff c α τ hc hατ)
  filter_upwards [hs, hd, hc', eventually_ge_atTop (2 : ℕ)] with N hNs hNd hNc hN2
  apply tailMass_le_model (by exact_mod_cast (show 1 < N by omega))
    hη hη1 hNd hδ.le hNc
  exact fun t ht => hT t (hNs.trans ht)

end
end Wu2004MeanValue

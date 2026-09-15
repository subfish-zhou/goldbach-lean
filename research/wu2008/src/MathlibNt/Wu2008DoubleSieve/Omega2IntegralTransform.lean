import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientSourceIntegral

/-!
# The fixed-cutoff coordinate in Wu04 (5.2)

The Buchstab prime coordinate is x = log(q)/log(p)-1. For the fixed
cutoff q^(1/t), the actual sieve ratio is t*x/(x+1), not x.
The change u=x/(x+1) gives the printed kernel 1/(u*(1-u)).
Only the coordinate is differentiated; the coefficient need not be continuous.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

theorem omega2_coordinate_monotone :
    MonotoneOn (fun x : ℝ => x / (x + 1)) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  apply (div_le_div_iff₀ (by linarith [hx] : 0 < x + 1)
    (by linarith [hy] : 0 < y + 1)).2
  nlinarith

theorem omega2_coordinate_mem {t x : ℝ} (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hx : x ∈ Icc (1 : ℝ) 10) :
    t * (x / (x + 1)) ∈ Icc (1 : ℝ) 10 := by
  have hx0 : 0 < x + 1 := by linarith [hx.1]
  have hlo : 1 / 2 ≤ x / (x + 1) := (le_div_iff₀ hx0).2 (by linarith [hx.1])
  have hhi : x / (x + 1) ≤ 1 := (div_le_one hx0).2 (by linarith)
  have ht0 : 0 ≤ t := by linarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo ht0]
  · nlinarith [mul_le_mul_of_nonneg_left hhi ht0]

theorem omega2_transformed_coefficient {f : ℝ → ℝ} {B t : ℝ}
    (hf : MonotoneOn f (Icc 1 10))
    (hB : ∀ x ∈ Icc (1 : ℝ) 10, |f x| ≤ B)
    (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    MonotoneOn (fun x => f (t * (x / (x + 1)))) (Icc 1 10) ∧
      ∀ x ∈ Icc (1 : ℝ) 10, |f (t * (x / (x + 1)))| ≤ B := by
  refine ⟨?_, fun x hx => hB _ (omega2_coordinate_mem ht ht5 hx)⟩
  intro x hx y hy hxy
  apply hf (omega2_coordinate_mem ht ht5 hx) (omega2_coordinate_mem ht ht5 hy)
  exact mul_le_mul_of_nonneg_left
    (omega2_coordinate_monotone (show 0 ≤ x by linarith [hx.1])
      (show 0 ≤ y by linarith [hy.1]) hxy)
    (by linarith)

theorem omega2_prime_coordinate {q p : ℝ} (hq : 1 < q) (hp : 1 < p) :
    (log q / log p - 1) / ((log q / log p - 1) + 1) =
      1 - log p / log q := by
  field_simp [(log_pos hq).ne', (log_pos hp).ne']
  ring

theorem omega2_integral_substitution (f : ℝ → ℝ) {s t : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) :
    (∫ x in (s - 1)..(t - 1), f (t * (x / (x + 1))) / x) =
      ∫ u in (1 - 1 / s)..(1 - 1 / t), f (t * u) / (u * (1 - u)) := by
  let F : ℝ → ℝ := fun x => x / (x + 1)
  have hab : s - 1 ≤ t - 1 := by linarith
  have hx0 (x : ℝ) (hx : x ∈ Icc (s - 1) (t - 1)) : 0 < x := by
    linarith [hx.1]
  have hc : ContinuousOn F (Icc (s - 1) (t - 1)) :=
    continuousOn_id.div (continuousOn_id.add continuousOn_const)
      (fun x hx => by change x + 1 ≠ 0; linarith [hx0 x hx])
  have hm : MonotoneOn F (Icc (s - 1) (t - 1)) :=
    omega2_coordinate_monotone.mono (fun x hx => (hx0 x hx).le)
  have hd : ∀ x ∈ Icc (s - 1) (t - 1),
      HasDerivWithinAt F (1 / (x + 1) ^ 2) (Icc (s - 1) (t - 1)) x := by
    intro x hx
    have h := (hasDerivAt_id x).div ((hasDerivAt_id x).add_const 1)
      (by linarith [hx0 x hx] : x + 1 ≠ 0)
    have h' : HasDerivAt F ((1 * (x + 1) - x * 1) / (x + 1) ^ 2) x := h
    have heq : (1 * (x + 1) - x * 1) / (x + 1) ^ 2 = 1 / (x + 1) ^ 2 := by ring
    rw [heq] at h'
    exact h'.hasDerivWithinAt
  have he (a : ℝ) (ha : 0 < a) : F (a - 1) = 1 - 1 / a := by
    dsimp [F]
    simp only [sub_add_cancel]
    field_simp [ha.ne']
  have huv := hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have hchange := integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Icc hd hm (fun u => f (t * u) / (u * (1 - u)))
  rw [hc.image_Icc_of_monotoneOn hab hm] at hchange
  rw [← he s (by linarith), ← he t (by linarith)]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le huv, ← integral_Icc_eq_integral_Ioc, hchange]
  apply (setIntegral_congr_fun measurableSet_Icc ?_).symm
  intro x hx
  dsimp [F]
  field_simp [(hx0 x hx).ne', (by linarith [hx0 x hx] : x + 1 ≠ 0)]
  ring

theorem omega2_source_prime_integral_uniform {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Q0 : ℝ, 1 < Q0 ∧ ∀ q : ℝ, Q0 ≤ q → ∀ f : ℝ → ℝ,
      MonotoneOn f (Set.Icc 1 10) →
      (∀ u ∈ Set.Icc (1 : ℝ) 10, |f u| ≤ B) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      |(∑ p ∈ primeWindow 1 (q ^ (1 / t)) (q ^ (1 / s)),
          f (t * (1 - log p / log q)) /
            (((p : ℝ) - 2) * (1 - log p / log q))) -
        ∫ u in (1 - 1 / s)..(1 - 1 / t), f (t * u) / (u * (1 - u))| ≤ ε := by
  obtain ⟨Q0, hQ0, hQ⟩ := primeCoefficient_source_log_uniform hB hε
  refine ⟨Q0, hQ0, ?_⟩
  intro q hq f hf hfb s t hs hst ht ht5
  obtain ⟨hm, hb⟩ := omega2_transformed_coefficient hf hfb ht ht5
  have h := hQ q hq _ hm hb s t hs hst (by linarith)
  rw [omega2_integral_substitution f hs hst] at h
  convert h using 2
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  dsimp [wuPrimeCoefficientWeight]
  rw [omega2_prime_coordinate (hQ0.trans_le hq)
    (by exact_mod_cast (mem_primeWindow.mp hp).1.one_lt)]

end Wu2008DoubleSieve

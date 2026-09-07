import MathlibNt.SieveTheory.LiLiuGoldbachG11ProductCoefficient
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKGoldbachRectangle

open Filter Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The existing literal normalized G11 coefficient supplies the order-one bound.
Neither primality of the output nor a new SW assumption enters this coefficient. -/
theorem goldbachG11NormalizedProductCoefficient_le_fouvryTau (N m : ℕ) :
    |goldbachG11NormalizedProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) m| ≤ (fouvryTau 1 m : ℝ) := by
  by_cases hm : m = 0
  · subst m
    have hz : 0 ∉ goldbachG11ProductSupport N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) := by
      intro h
      exact (Nat.lt_irrefl 0) (goldbachG11ProductSupport_data h).1
    rw [goldbachG11NormalizedProductCoefficient_eq_zero_of_not_mem hz]
    simp
  · rw [fouvryTau_order_one hm, Nat.cast_one,
      abs_of_nonneg (goldbachG11NormalizedProductCoefficient_nonneg N m _ _)]
    exact goldbachG11NormalizedProductCoefficient_le_one N m

/-- The proved prime-SW Fouvry rectangle, now instantiated with the actual G11
coefficient. The same individual signed WF member is retained on the full level. -/
theorem goldbachG11_normalized_Fouvry_rectangle (j A : ℕ) {Cscale η : ℝ}
    (hCscale : 1 ≤ Cscale) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : PrimeC2Interval, ∀ M ν : ℝ,
      1 ≤ M → 4*M*z.scale = x → η ≤ ν → ν ≤ 1/10+η/10 → z.scale = x^ν →
      ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x →
      ∀ U : Finset ℕ, (∀ m ∈ U, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*M) →
      ∀ c : ℕ → ℝ, SignedWellFactorable j (x^((5-5*ν)/9-η)) c →
        |signedError U (primeSWInterval z.lower z.upper)
          (Ioc 0 ⌊x^((5-5*ν)/9-η)⌋₊)
          (goldbachG11NormalizedProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
            ((N : ℝ)^(4/33 : ℝ)))
          (fun p => if p.Coprime N then primeSWBeta p else 0) c (N : ℤ)| ≤
          x/Real.log x^A := by
  filter_upwards [primeC2_goldbach_rectangle_kscale 1 j A hCscale hη] with x hx
  intro z M ν hM hMT hην hν hT N hN hNx U hU c hc
  exact hx z M ν hM hMT hην hν hT N hN hNx U hU _ c
    (fun m _ => goldbachG11NormalizedProductCoefficient_le_fouvryTau N m) hc

/-- Exact scalar transport of the entire signed error; no absolute-value triangle. -/
theorem goldbachG11_signedError_mul_alpha (U V Q : Finset ℕ)
    (α β c : ℕ → ℝ) (a : ℤ) (k : ℝ) :
    signedError U V Q (fun m => k*α m) β c a = k*signedError U V Q α β c a := by
  have hd (q : ℕ) : bilinearDiscrepancy U V (fun m => k*α m) β a q =
      k*bilinearDiscrepancy U V α β a q := by
    simp only [bilinearDiscrepancy, mul_sub, ← mul_div_assoc, mul_sum, mul_ite,
      mul_zero, mul_assoc]
  unfold signedError
  rw [mul_sum]
  apply sum_congr rfl
  intro q _hq
  rw [hd]
  ring

/-- All original labelled multiplicities are restored exactly. -/
theorem goldbachG11_signedError_productCoefficient (N : ℕ) (U V Q : Finset ℕ)
    (β c : ℕ → ℝ) :
    signedError U V Q
      (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ)) β c N =
      400*signedError U V Q
        (goldbachG11NormalizedProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
          ((N : ℝ)^(4/33 : ℝ))) β c N := by
  have he : (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ)) =
      (fun m => 400*goldbachG11NormalizedProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m) := by
    funext m
    exact (goldbachG11NormalizedProductCoefficient_mul_four_hundred N m _ _).symm
  rw [he, goldbachG11_signedError_mul_alpha]

/-- Actual unnormalized G11 rectangle discrepancy, with the factor 400 paid
by one extra logarithm. The coefficient and its original multiplicities stay intact. -/
theorem goldbachG11_Fouvry_rectangle (j A : ℕ) {Cscale η : ℝ}
    (hCscale : 1 ≤ Cscale) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : PrimeC2Interval, ∀ M ν : ℝ,
      1 ≤ M → 4*M*z.scale = x → η ≤ ν → ν ≤ 1/10+η/10 → z.scale = x^ν →
      ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x →
      ∀ U : Finset ℕ, (∀ m ∈ U, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*M) →
      ∀ c : ℕ → ℝ, SignedWellFactorable j (x^((5-5*ν)/9-η)) c →
        |signedError U (primeSWInterval z.lower z.upper)
          (Ioc 0 ⌊x^((5-5*ν)/9-η)⌋₊)
          (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
            ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
          (fun p => if p.Coprime N then primeSWBeta p else 0) c (N : ℤ)| ≤
          x/Real.log x^A := by
  filter_upwards [goldbachG11_normalized_Fouvry_rectangle j (A+1) hCscale hη,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (400 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with x hx hlog hx0
  intro z M ν hM hMT hην hν hT N hN hNx U hU c hc
  have hn := hx z M ν hM hMT hην hν hT N hN hNx U hU c hc
  rw [goldbachG11_signedError_productCoefficient, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 400)]
  have hp : 0 < Real.log x := by linarith
  have hpay : 400*(x/Real.log x^(A+1)) ≤ x/Real.log x^A := by
    rw [pow_succ]
    apply (le_div_iff₀ (pow_pos hp A)).2
    have he : 400*(x/(Real.log x^A*Real.log x))*Real.log x^A =
        400*x/Real.log x := by field_simp
    rw [he]
    exact (div_le_iff₀ hp).2 (by nlinarith)
  exact (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 400)).trans hpay

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
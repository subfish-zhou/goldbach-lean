import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientSourceGeometry
import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientLogSubstitution

/-!
# The source prime-summation formula with its complete uniform error

Wu04, TeX 1101--1106. The estimate consumes true-li PNT, discontinuous
right-endpoint quadrature, exact half-open endpoints, the p-2 correction,
and the logarithmic Jacobian. The bound precedes the coefficient.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology Interval

theorem wuPrime_source_cutoff_parameter {q u : ℝ} (hq : 1 < q) :
    log q / log (q ^ (1 / u)) - 1 = u - 1 := by
  rw [log_rpow (by linarith : 0 < q)]
  field_simp [(log_pos hq).ne']

/-- The fully integrated source prime-sum formula. The single threshold
works for signed, discontinuous coefficients and for all 2≤s≤t≤10. -/
theorem primeCoefficient_source_log_uniform {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Q0 : ℝ, 1 < Q0 ∧ ∀ q : ℝ, Q0 ≤ q → ∀ f : ℝ → ℝ,
      MonotoneOn f (Set.Icc 1 10) →
      (∀ u ∈ Set.Icc (1 : ℝ) 10, |f u| ≤ B) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      |(∑ p ∈ primeWindow 1 (q ^ (1 / t)) (q ^ (1 / s)),
          wuPrimeCoefficientWeight f q p) -
        ∫ u in (s - 1)..(t - 1), f u / u| ≤ ε := by
  obtain ⟨Q1, hQ1, hcontinuous⟩ :=
    primeCoefficient_source_continuous_uniform hB (half_pos hε)
  obtain ⟨Q2, _, hgeometry⟩ := primeCoefficient_source_geometry 0
  have hevent : ∀ᶠ q : ℝ in atTop, 160 * B / ε ≤ log q :=
    tendsto_log_atTop.eventually (eventually_ge_atTop _)
  obtain ⟨Q3, hQ3⟩ := eventually_atTop.mp hevent
  refine ⟨max Q1 (max Q2 Q3), hQ1.trans_le (le_max_left _ _), ?_⟩
  intro q hq f hf hfb s t hs hst ht
  have h1 : Q1 ≤ q := (le_max_left _ _).trans hq
  have h2 : Q2 ≤ q := (le_max_left _ _).trans ((le_max_right _ _).trans hq)
  have h3 : Q3 ≤ q := (le_max_right _ _).trans ((le_max_right _ _).trans hq)
  have hq1 : 1 < q := hQ1.trans_le h1
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  obtain ⟨hY0, hYZ, _, ha4, _, hlq, hZ, _, _⟩ := hgeometry q h2 s t hs hst ht
  have hCY : 0 < ⌈q ^ (1 / t)⌉₊ := Nat.ceil_pos.mpr hY0
  have hlow := (Nat.ceil_eq_iff hCY.ne').mp (rfl : ⌈q ^ (1 / t)⌉₊ = ⌈q ^ (1 / t)⌉₊)
  have hY4 : 4 ≤ q ^ (1 / t) :=
    (by exact_mod_cast ha4 : (4 : ℝ) ≤ (⌈q ^ (1 / t)⌉₊ - 1 : ℕ)).trans hlow.1.le
  have hkernel := wuPrimeRealWeight_log_error hf hq1 hY4 hYZ hZ
    (by rw [wuPrime_source_cutoff_parameter hq1]; linarith) hB hfb
  rw [wuPrime_source_cutoff_parameter hq1,
    wuPrime_source_cutoff_parameter hq1] at hkernel
  have hlogY : log (q ^ (1 / t)) = log q / t := by
    rw [log_rpow (by linarith : 0 < q)]
    ring
  have hlogY0 : 0 < log (q ^ (1 / t)) := log_pos (by linarith)
  have hloglower : log q / 10 ≤ log (q ^ (1 / t)) := by
    rw [hlogY]
    exact div_le_div_of_nonneg_left (log_pos hq1).le ht0 ht
  have hpay : 8 * B / (q ^ (1 / t)) / log (q ^ (1 / t)) ≤ ε / 2 := by
    apply (div_le_iff₀ hlogY0).2
    have hb : 8 * B / (q ^ (1 / t)) ≤ 8 * B :=
      div_le_self (by positivity) (by linarith)
    have hlarge := (div_le_iff₀ hε).1 (hQ3 q h3)
    have hmul := mul_le_mul_of_nonneg_left hloglower hε.le
    nlinarith
  have hmain := hcontinuous q h1 f hf hfb s t hs hst ht
  have htotal := (abs_sub_le
    (∑ p ∈ primeWindow 1 (q ^ (1 / t)) (q ^ (1 / s)), wuPrimeCoefficientWeight f q p)
    (∫ x in (q ^ (1 / t))..(q ^ (1 / s)), wuPrimeRealWeight f q x / log x)
    (∫ u in (s - 1)..(t - 1), f u / u)).trans (add_le_add hmain (hkernel.trans hpay))
  linarith

end Wu2008DoubleSieve

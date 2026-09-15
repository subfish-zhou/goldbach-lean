import MathlibNt.Wu2008DoubleSieve.SingleUpperQuadrature

/-! Uniform bounded-Lipschitz quadrature on the actual low-alpha slab.
Only the rescaling step is generalized; the accepted sources are unchanged. -/
namespace Wu2008DoubleSieve.SeventhEighth
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology

/-- One threshold precedes the function and both endpoints. The statement
allows the eighth outer coordinate alpha, which is below one tenth. -/
theorem classical_low_weighted_uniform (M K ε : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (f : ℝ → ℝ) (a b : ℝ),
      ContinuousOn f (Icc (1 / 15 : ℝ) (1 / 3)) →
      (∀ t ∈ Icc (1 / 15 : ℝ) (1 / 3), |f t| ≤ M) →
      (∀ x ∈ Icc (1 / 15 : ℝ) (1 / 3), ∀ y ∈ Icc (1 / 15 : ℝ) (1 / 3),
        |f x - f y| ≤ K * |x - y|) →
      1 / 15 ≤ a → a ≤ b → b ≤ 1 / 3 →
      |primeOrderedClosedSum N a b f - ∫ t in a..b, f t / t| < ε := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (2 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (ht.eventually (primeOrdered_weighted_uniform M K ε hM hK hε))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN f a b hc hbnd hlip ha hab hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hmap (t : ℝ) (ht : t ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
      (2 / 3) * t ∈ Icc (1 / 15 : ℝ) (1 / 3) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc' := hc.comp (by fun_prop :
    ContinuousOn (fun t : ℝ => (2 / 3) * t) (Icc (1 / 10 : ℝ) (1 / 2))) hmap
  have hlip' : ∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |f ((2 / 3) * x) - f ((2 / 3) * y)| ≤ K * |x - y| := by
    intro x hx y hy
    have h := hlip _ (hmap x hx) _ (hmap y hy)
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)] at h
    nlinarith [mul_nonneg hK (abs_nonneg (x - y))]
  have h := hT N ((le_max_right _ _).trans hN) (fun t => f ((2 / 3) * t))
    (3 / 2 * a) (3 / 2 * b) hc' (fun t ht => hbnd _ (hmap t ht)) hlip'
    (by linarith) (by linarith) (by linarith)
  rw [SingleUpperQuadrature.rescaled_integral] at h
  have he (t : ℝ) : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ (3 / 2 * t) = (N : ℝ) ^ t := by
    rw [← rpow_mul hN0.le, show (2 / 3 : ℝ) * (3 / 2 * t) = t by ring]
  have htlog (p : ℕ) :
      (2 / 3) * (log (p : ℝ) / log ((N : ℝ) ^ (2 / 3 : ℝ))) = log p / log N := by
    rw [log_rpow hN0]
    field_simp
  simpa only [primeOrderedClosedSum, he, htlog] using h

end Wu2008DoubleSieve.SeventhEighth

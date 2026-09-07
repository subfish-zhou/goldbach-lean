import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeC2

noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Literal Goldbach residue and literal coprimality-filtered prime coefficient.
This is a rectangular contribution, not the curved G9 region. -/
theorem primeC2_goldbach_rectangle (i j A : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ z : PrimeC2Interval, ∀ M ν : ℝ,
      1 ≤ M → 4*M*z.scale = x → ε ≤ ν → ν ≤ 1/10 → z.scale = x^ν →
      ∀ N : ℕ, 0 < N → (N : ℝ) ≤ x →
      ∀ U : Finset ℕ, (∀ n ∈ U, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*M) →
      ∀ α c : ℕ → ℝ, (∀ n ∈ U, |α n| ≤ (fouvryTau i n : ℝ)) →
      SignedWellFactorable j (x^((5-5*ν)/9-ε)) c →
      |signedError U (primeSWInterval z.lower z.upper)
        (Ioc 0 ⌊x^((5-5*ν)/9-ε)⌋₊) α
        (fun n => if n.Coprime N then primeSWBeta n else 0) c (N : ℤ)| ≤
        x/Real.log x^A := by
  filter_upwards [primeC2_clean_unconditional i j A hε hε,
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro z M ν hM hMT hεν hν hT N hN hNx U hU α c hα hc
  let idx : BetaCleanIndex PrimeC2Interval.scale ε :=
    { index := z
      residue := N
      scale := x
      one_le_T := z.one_le_scale
      one_le_scale := hx1
      residue_ne_zero := by exact_mod_cast hN.ne'
      residue_le_scale := by simpa using hNx
      scale_rpow_le := by rw [hT]; exact Real.rpow_le_rpow_of_exponent_le hx1 hεν }
  have he := hx idx M ν hM hMT hεν hν hT U hU α c hα hc (N : ℤ)
    (by exact_mod_cast hN.ne') (by simpa using hNx)
  have hfun : betaClean primeSWBeta (N : ℤ) =
      (fun n => if n.Coprime N then primeSWBeta n else 0) := funext (primeSWBeta_clean_nat N)
  simpa only [idx, hfun] using he

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

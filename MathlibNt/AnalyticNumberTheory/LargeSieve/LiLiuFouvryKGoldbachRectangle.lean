import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeC2
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKC2
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKCleanScale

noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Literal Goldbach residue and literal coprimality-filtered prime coefficient.
This is a rectangular contribution, not the curved G9 region. -/
theorem primeC2_goldbach_rectangle_kscale (i j A : ℕ) {Cscale ε : ℝ}
    (hCscale : 1 ≤ Cscale) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ z : PrimeC2Interval, ∀ M ν : ℝ,
      1 ≤ M → 4*M*z.scale = x → ε ≤ ν → ν ≤ 1/10+ε/10 → z.scale = x^ν →
      ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x →
      ∀ U : Finset ℕ, (∀ n ∈ U, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*M) →
      ∀ α c : ℕ → ℝ, (∀ n ∈ U, |α n| ≤ (fouvryTau i n : ℝ)) →
      SignedWellFactorable j (x^((5-5*ν)/9-ε)) c →
      |signedError U (primeSWInterval z.lower z.upper)
        (Ioc 0 ⌊x^((5-5*ν)/9-ε)⌋₊) α
        (fun n => if n.Coprime N then primeSWBeta n else 0) c (N : ℤ)| ≤
        x/Real.log x^A := by
  have hhalf : 0 < ε/2 := by positivity
  have hbound := direct_wellFactorable_signedError_kscale (i := i) (j := j) (k := 1) A
    (primeC2_clean_family hhalf) (fun z => z.one_le_T)
    (fun z => primeC2Interval_support z.index)
    (fun z n _ => (abs_betaClean_le _ _ _).trans (primeSWBeta_le_order_one n)) hCscale hε
  filter_upwards [hbound, eventually_ge_atTop Cscale] with x hx hxC
  have hx1 : 1 ≤ x := hCscale.trans hxC
  intro z M ν hM hMT hεν hν hT N hN hNx U hU α c hα hc
  let idx : BetaCleanIndex PrimeC2Interval.scale (ε/2) :=
    { index := z
      residue := N
      scale := Cscale*x
      one_le_T := z.one_le_scale
      one_le_scale := by nlinarith
      residue_ne_zero := by exact_mod_cast hN.ne'
      residue_le_scale := by simpa using hNx
      scale_rpow_le := by
        apply (kClean_aux_scale_rpow_le hCscale hxC hε).trans
        rw [hT]
        exact Real.rpow_le_rpow_of_exponent_le hx1 hεν }
  have he := hx idx M ν hM hMT hεν hν hT U hU α c hα hc (N : ℤ)
    (by exact_mod_cast hN.ne') (by simpa using hNx)
  have hfun : betaClean primeSWBeta (N : ℤ) =
      (fun n => if n.Coprime N then primeSWBeta n else 0) := funext (primeSWBeta_clean_nat N)
  simpa only [idx, hfun] using he

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

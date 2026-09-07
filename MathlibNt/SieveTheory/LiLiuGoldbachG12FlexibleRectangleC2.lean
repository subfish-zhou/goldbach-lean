import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleRectangle

open Filter Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace G12FlexibleRectangle

/-- The physical rectangle is the exact C2 input with unchanged source scale T. -/
theorem rectangle_C2_input (N : ℕ) (ε : ℝ) (M U T V : ℕ)
    (hT : 1 ≤ T) (hTV : T ≤ V) (hV : V ≤ 2*T)
    (Q : Finset ℕ) (c : ℕ → ℝ) :
    discrepancy N (rectangle N ε M U T V) Q c =
      signedError (Ioc M U)
        (primeSWInterval (shortInterval T V hT hTV hV).lower
          (shortInterval T V hT hTV hV).upper)
        Q (alpha N ε T V) (fun r => if r.Coprime N then primeSWBeta r else 0)
        c (N : ℤ) := by
  rw [shortInterval_support]
  exact rectangle_signedError N ε M U T V Q c

/-- Uniform threshold precedes every endpoint, the physical epsilon and c.
There is no lower bound on either cell width. The boundary is not estimated. -/
theorem rectangle_C2_bound (j A : ℕ) {Cscale ζ : ℝ}
    (hCscale : 1 ≤ Cscale) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in atTop, ∀ M U T V : ℕ,
      1 ≤ M → M ≤ U → U ≤ 2*M → 1 ≤ T → T ≤ V → V ≤ 2*T →
      ∀ ν : ℝ, 4*(M : ℝ)*T = x → ζ ≤ ν → ν ≤ 1/10+ζ/10 →
      (T : ℝ) = x^ν → ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x →
      ∀ ε : ℝ, ∀ c : ℕ → ℝ, SignedWellFactorable j (x^((5-5*ν)/9-ζ)) c →
        |discrepancy N (rectangle N ε M U T V) (Ioc 0 ⌊x^((5-5*ν)/9-ζ)⌋₊) c| ≤
          x/Real.log x^A := by
  filter_upwards [primeC2_goldbach_rectangle_kscale 1 j A hCscale hζ] with x hx
  intro M U T V hM _ hU hT hTV hV ν hprod hν hνu hscale N hN hNC ε c hc
  rw [rectangle_C2_input N ε M U T V hT hTV hV]
  exact hx (shortInterval T V hT hTV hV) M ν (by exact_mod_cast hM)
    hprod hν hνu hscale N hN hNC (Ioc M U)
    (fun m hm => G12LowRectangle.long_support_geometry M m
      (mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2.trans hU⟩))
    (alpha N ε T V) c (fun m hm => alpha_tau N ε M U T V m hm) hc

end G12FlexibleRectangle

import MathlibNt.SieveTheory.LiLiuGoldbachG12LowRectangle

open Filter Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace G12LowRectangle

/-- The actual finite rectangle consumes the proved prime-C2 source. Its
unpaid boundary and the later common-family density remain separate obligations. -/
theorem rectangle_C2_bound (j A : ℕ) {Cscale ζ : ℝ}
    (hCscale : 1 ≤ Cscale) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in atTop, ∀ M T : ℕ, 1 ≤ M → 1 ≤ T →
      ∀ ν : ℝ, 4*(M : ℝ)*T = x → ζ ≤ ν → ν ≤ 1/10+ζ/10 →
      (T : ℝ) = x^ν → ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x →
      ∀ ε : ℝ, ∀ c : ℕ → ℝ, SignedWellFactorable j (x^((5-5*ν)/9-ζ)) c →
        |discrepancy N (rectangle N ε M T) (Ioc 0 ⌊x^((5-5*ν)/9-ζ)⌋₊) c| ≤
          x/Real.log x^A := by
  filter_upwards [primeC2_goldbach_rectangle_kscale 1 j A hCscale hζ] with x hx
  intro M T hM hT ν hprod hν hνu hscale N hN hNC ε c hc
  rw [rectangle_C2_input N ε M T hT]
  exact hx (shortInterval T hT) M ν (by exact_mod_cast hM) hprod hν hνu hscale
    N hN hNC (Ioc M (2*M)) (fun m hm => long_support_geometry M m hm)
    (alpha N ε T) c (fun m hm => alpha_tau N ε M T m hm) hc

end G12LowRectangle

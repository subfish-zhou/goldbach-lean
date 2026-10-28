import Mathlib.Topology.Order.LeftRight
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedRosser
import MathlibNt.SieveTheory.LiLiuGoldbachG11NormalizedIntegralEnvelope

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
namespace G12ClippedWindow

/-- Choose a fixed loss before every varying clipped profile. -/
theorem choose_eight_loss (δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ 8*(1+t)^3 ≤ 8+δ := by
  let f : ℝ → ℝ := fun t => 8*(1+t)^3
  have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop
  have he := hc.eventually (gt_mem_nhds (lt_add_of_pos_right (f 0) hδ))
  obtain ⟨t,ht,ht1,hf⟩ := ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).and he).exists_gt
  exact ⟨t,ht,ht1.le,by simpa [f] using hf.le⟩

/-- The second logarithm for the actual ungated clipped prime outputs.
No hypothesis on epsilon's sign or fixed-window choice is required. -/
theorem primeOutput_uniformEight (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (_hEven : Even N)
      (g L U : ℕ → ℝ) (ε : ℝ), Admissible N ε g L U →
      primeOutput N g L U ≤
        (8+δ)*400*mass N g L U*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) +
        δ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨t,ht,ht1,htloss⟩ := choose_eight_loss δ hδ
  have hρ : 0 < t*Real.exp Real.eulerMascheroniConstant := mul_pos ht (Real.exp_pos _)
  obtain ⟨B,C,z₀,hB,_hC,K,hK,hpaid⟩ := primeOutput_le_paidRosser 3
    (t*Real.exp Real.eulerMascheroniConstant) (by norm_num) hρ
  obtain ⟨G,_,hgeom⟩ := goldbachG11SieveParameters_eventually B z₀ t hB.le ht ht1
  obtain ⟨E,_,heuler⟩ := goldbachG11EulerFactor_normalized B t hB.le ht ht1
  obtain ⟨S,_,hsmall⟩ := goldbachG11_smallOutput_paid (δ/2) (by positivity)
  obtain ⟨R,herr⟩ := eventually_atTop.mp
    (goldbachG11NormalizedIntegral_logError_paid (400*C) (δ/2) (by positivity))
  refine ⟨max K (max G (max E (max S R))),by omega,?_⟩
  intro N hN hEven g L U ε h
  have hN4 : 4 ≤ N := by omega
  obtain ⟨hZ,hZq,hΔ,hs,hlevel,hlogZ,_⟩ := hgeom N (by omega)
  have hZ0 : 0 ≤ goldbachG11SieveCutoff B N := (by norm_num : (0 : ℝ) ≤ 2).trans
    ((le_max_left _ _).trans hZ)
  have hp := hpaid N (by omega) hEven g L U ε
    (goldbachG11SieveCutoff B N) (goldbachG11SieveLevel B N) 2 h
    ((le_max_right _ _).trans hZ) ((le_max_left _ _).trans hZ) hΔ hs
    (by norm_num) (by norm_num) hlevel
  have hF : jurkatRichertUpperLinearSieveFactor (2 : ℝ) = Real.exp Real.eulerMascheroniConstant := by
    norm_num [jurkatRichertUpperLinearSieveFactor]
  rw [hF] at hp
  have he := heuler N (by omega) hEven
  have hx := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0 : ℝ) ≤ 400) (mass_nonneg h))
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale : 0 ≤ 400*mass N g L U*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mass_nonneg h))
      (SingularSeries.liuSingularSeries_pos N).le) hlogN.le
  have hloss := mul_le_mul_of_nonneg_right htloss hscale
  have hsm := hsmall N (by omega) (goldbachG11SieveCutoff B N) hZ0 hZq
  have her := herr N (by omega)
  ring_nf at hp hx hloss hsm her ⊢
  linarith only [hp,hx,hloss,hsm,her]

/-- Literal high source prime outputs; the source mass remains ungated. -/
def highPrimeOutput (N : ℕ) (ε : ℝ) : ℝ :=
  400 * ∑ m ∈ goldbachG12ActiveProductSupport N, goldbachG12NormalizedCoefficient N m *
    (((G12LowHighOutput.highWindow N ε m).filter (fun r => (N-r*m).Prime)).card : ℝ)

theorem highPrimeOutput_uniformEight (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ),
      highPrimeOutput N ε ≤
        (8+δ)*400*highMass N ε*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) +
        δ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨K,hK,h⟩ := primeOutput_uniformEight δ hδ
  refine ⟨K,hK,?_⟩
  intro N hN hEven ε
  have hp := h N hN hEven (goldbachG12NormalizedCoefficient N)
    (G12LowHighOutput.highLo N ε) (goldbachG11PiLiHi N) ε (high_admissible (by omega) ε)
  simpa only [primeOutput,mass,high_window,highPrimeOutput,highMass] using hp

end G12ClippedWindow

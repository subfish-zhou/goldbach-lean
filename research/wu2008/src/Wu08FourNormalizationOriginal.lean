import Wu08FourNormalizationLow
import MathlibNt.SieveTheory.LiLiuFouvryG9AnalyticDensity

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace Wu08FirstPrimeFour.Normalization

/-- Proper original-N prime carrier; not the full integer interval. -/
def properPrimes (N : ℕ) : Finset ℕ := fouvryG9SievePrimes N (sqrt N)

def properMain (N : ℕ) (e : Bool) (ξ ρ δ η : ℝ) : ℝ :=
  ∑ k ∈ occupied N e ξ ρ, cellMain N e ξ ρ δ η (sqrt N) (properPrimes N) k

/-- No tag, signed exceptional, or low-output residue remains here.
Large first primes and fixed-xi prefixes have NOT been paid or omitted. -/
def properPairCore (N : ℕ) (ξ ρ δ η : ℝ) : ℝ :=
  ((large N false).card : ℝ)+(large N true).card+
  (smallPrefix N false ξ).card+(smallPrefix N true ξ).card+
  properMain N false ξ ρ δ η+properMain N true ξ ρ δ η

/-- The original finite amount now has all its additive rectangle errors paid.
Same xi,rho,delta,eta and SAME signed family are retained. -/
theorem originalPairAmount_paid (A : ℕ) {ξ ρ δ η : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hδ : 0 ≤ δ) (hδu : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      originalPairAmount N ξ ρ δ η (A+6) (fun _ _ => properPrimes N) (fun _ _ => sqrt N) ≤
        properPairCore N ξ ρ δ η+(N : ℝ)/log (N : ℝ)^A := by
  obtain ⟨Nc,hc⟩ := cellAmount_total (A+1) hξ hξ1 hρ hρu hδ hδu hη hηu
  obtain ⟨Nl,hlow⟩ := low_total (A+1) hρ
  refine ⟨max Nc (max Nl (exp 4)),?_⟩
  intro N hN
  have hNc := (le_max_left _ _).trans hN
  have hNl := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNe := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hl : 4 ≤ log (N : ℝ) := by simpa only [log_exp] using log_le_log (exp_pos 4) hNe
  have hfamily : ∀ e : Bool,
      (∑ k ∈ occupied N e ξ ρ, cellAmount N e ξ ρ δ η (sqrt N) (A+6) (properPrimes N) k) ≤
        properMain N e ξ ρ δ η+2*((N : ℝ)/log (N : ℝ)^(A+1)) := by
    intro e
    have hc' := hc N hNc e (fun _ => properPrimes N) (fun _ => sqrt N)
    have hl' := hlow N hNl e ξ (fun _ => sqrt N)
      (fun _ _ => ⟨sqrt_nonneg _,by rw [sqrt_eq_rpow]⟩)
    change _ ≤ properMain N e ξ ρ δ η+_+_ at hc'
    linarith only [hc',hl']
  have hpay : 4*((N : ℝ)/log (N : ℝ)^(A+1)) ≤ (N : ℝ)/log (N : ℝ)^A := by
    have hp : 0 < log (N : ℝ) := by linarith
    apply (le_div_iff₀ (pow_pos hp A)).mpr
    rw [pow_succ]
    field_simp
    nlinarith
  have h10 := hfamily false
  have h11 := hfamily true
  unfold originalPairAmount properPairCore
  linarith only [h10,h11,hpay]

/-- Actual original Q10+Q11 producer after all new rectangle payments.
The original raw-to-physical exception is charged once, not once per branch. -/
theorem original_pair_paid_upper (A : ℕ) {ξ ρ ε δ η κ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hε : 0 < ε) (hεa : ε < truncatedSixthLowerAlpha) (hεδ : ε < δ)
    (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8) (hκ : 0 < κ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
        properPairCore N ξ ρ δ η+(N : ℝ)/log (N : ℝ)^A+
          κ*wuSingularSeries N*N/log N^2 := by
  obtain ⟨Nu,hu⟩ := original_pair_global_level_upper (A+6) hξ hξ1 hε hεa hεδ hδ hη hηu hκ
  obtain ⟨Np,hp⟩ := originalPairAmount_paid A hξ hξ1 hρ hρu
    (hε.le.trans hεδ.le) hδ hη hηu
  refine ⟨max Nu Np,?_⟩
  intro N hN he
  have hraw := hu N ((le_max_left _ _).trans hN) he ρ hρ hρu
    (fun _ _ => properPrimes N) (fun _ _ => sqrt N)
    (fun _ _ _ p hp => (fouvryG9SievePrimes_mem N p (sqrt N) |>.mp hp).1)
    (fun _ _ _ p hp => (fouvryG9SievePrimes_mem N p (sqrt N) |>.mp hp).2.1)
    (fun _ _ _ p hp => (fouvryG9SievePrimes_mem N p (sqrt N) |>.mp hp).2.2)
  exact hraw.trans (add_le_add (hp N ((le_max_right _ _).trans hN)) le_rfl)

#print axioms originalPairAmount_paid
#print axioms original_pair_paid_upper
end Wu08FirstPrimeFour.Normalization

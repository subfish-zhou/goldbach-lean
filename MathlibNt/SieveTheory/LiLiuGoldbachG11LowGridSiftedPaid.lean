import MathlibNt.SieveTheory.LiLiuGoldbachG11LowGridFamilyError
import MathlibNt.SieveTheory.LiLiuGoldbachG11LowGridTransportCost
import MathlibNt.SieveTheory.LiLiuGoldbachG11GridRemainderMajorant
import MathlibNt.SieveTheory.LiLiuGoldbachG11RectangleFullTransport

open Finset
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The exact low-grid main term, before arithmetic density/Euler normalization. -/
def goldbachG11LowGridDensityMain (N : ℕ) (ε δ θ ρ : ℝ)
    (P : (ℕ × ℕ) → Finset ℕ) (z : (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ k ∈ goldbachG11LowGridUsed N ε ρ,
    ∑ m ∈ goldbachG11GridLong N ε ρ k, ∑ p ∈ goldbachG11GridShort N ρ k,
      goldbachG11RectangleWeight N (m,p)*externalDensity true (P k)
        (externalInternalLevel (goldbachG11GridLowLevel N δ ρ k) θ) θ (z k)
        (progressionDensity (m*p))

/-- Actual low-grid sifted counts with all distribution and primorial/full
transport errors paid. Only structural conditions on the changing sieve remain. -/
theorem goldbachG11LowGrid_sifted_paid (A : ℕ) {ε δ θ ρ : ℝ}
    (hε : 0 < ε) (hεu : ε ≤ 1) (hδ : 0 < δ) (hδu : δ < 1/2)
    (hθ : 0 < θ) (hθu : θ < 1/8) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ (P : (ℕ × ℕ) → Finset ℕ) (z : (ℕ × ℕ) → ℝ),
      (∀ k ∈ goldbachG11LowGridUsed N ε ρ, ∀ p ∈ P k, p.Prime) →
      (∀ k ∈ goldbachG11LowGridUsed N ε ρ, ∀ p ∈ P k, p.Coprime N) →
      (∀ k ∈ goldbachG11LowGridUsed N ε ρ, ∀ p ∈ P k, (p : ℝ) < z k) →
      (∑ k ∈ goldbachG11LowGridUsed N ε ρ,
        goldbachG11RectangleSiftedMass N (goldbachG11GridLong N ε ρ k)
          (goldbachG11GridShort N ρ k) (P k)) ≤
        goldbachG11LowGridDensityMain N ε δ θ ρ P z + 2*(N : ℝ)/Real.log (N : ℝ)^A := by
  let μ := g9TransportMu δ θ
  obtain ⟨C,hC,hmajor⟩ := goldbachG11Grid_remainder_majorant (g9TransportMu_pos hδu hθ)
  obtain ⟨Nf,hf⟩ := goldbachG11LowGrid_externalFamily_error_total A hε hεu hδ hδu hθ hθu hρ hρu
  obtain ⟨Nt,ht⟩ := goldbachG11LowGrid_transport_envelope_paid A hδ.le hδu hθ hθu hρ hρu hC
  obtain ⟨Ng,hg⟩ := goldbachG11LowGrid_internal_gates hδ.le hδu hθ hρ hρu
  refine ⟨max Nf (max Nt Ng),?_⟩
  intro N hN P z hP hPN hcut
  obtain ⟨hNf,hrest⟩ := max_le_iff.mp hN
  obtain ⟨hNt,hNg⟩ := max_le_iff.mp hrest
  let K := goldbachG11LowGridUsed N ε ρ
  let D := fun k => externalInternalLevel (goldbachG11GridLowLevel N δ ρ k) θ
  let H : ℝ := C*(N : ℝ)^(1+μ)
  let main := fun k => ∑ m ∈ goldbachG11GridLong N ε ρ k,
    ∑ p ∈ goldbachG11GridShort N ρ k,
      goldbachG11RectangleWeight N (m,p)*externalDensity true (P k) (D k) θ (z k)
        (progressionDensity (m*p))
  let E := fun k => ∑ t ∈ externalTags true (P k) (D k) θ (z k),
    |signedError (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k)
      (Ioc 0 ⌊goldbachG11GridLowLevel N δ ρ k⌋₊)
      (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
      (fun p => if p.Coprime N then primeSWBeta p else 0)
      (fun d => externalTerm true (P k) (D k) θ (z k) t d) N|
  let Z := fun k => Real.exp (8*(θ⁻¹)^3)*H*(4/(D k)^(θ^2))*
    (1+Real.log (⌊goldbachG11GridLowLevel N δ ρ k⌋₊ : ℝ))^2
  have hpoint : ∀ k ∈ K,
      goldbachG11RectangleSiftedMass N (goldbachG11GridLong N ε ρ k)
        (goldbachG11GridShort N ρ k) (P k) ≤ main k+E k+Z k := by
    intro k hk
    obtain ⟨hn,hbig,hq,hd,hqn⟩ := hg N hNg ε k hk
    have hq0 := zero_le_one.trans hq
    have hH : 0 ≤ H := by dsimp [H]; positivity
    have hr : ∀ d ∈ Icc 1 ⌊goldbachG11GridLowLevel N δ ρ k⌋₊,
        |bilinearDiscrepancy (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k)
          (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
            ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
          (fun p => if p.Coprime N then primeSWBeta p else 0) N d| ≤ H/d.totient := by
      intro d hd'
      have hdN : d ≤ N := by
        have he := ((Nat.le_floor_iff hq0).mp (mem_Icc.mp hd').2).trans hqn
        exact_mod_cast he
      exact hmajor N (by exact_mod_cast hn) ε ρ hρ hρu hbig k
        (mem_filter.mp hk).1 d (mem_Icc.mp hd').1 hdN
    have hu := goldbachG11Rectangle_upper_transport N
      (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k) (P k)
      (hP k hk) (hPN k hk) hq0 hd hθ hθu (hcut k hk) hH hr
    dsimp only at hu
    have hcard := (externalTags_card_and_wellFactorable true (P k) (z k) hd hθ hθu).1.le
    have hb : ((externalTags true (P k) (D k) θ (z k)).card : ℝ)*H*
        (4/(D k)^(θ^2))*(1+Real.log (⌊goldbachG11GridLowLevel N δ ρ k⌋₊ : ℝ))^2 ≤ Z k := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hH) (by positivity))
        (sq_nonneg _)
    exact hu.trans (add_le_add (le_refl _) hb)
  have hE : (∑ k ∈ K, E k) ≤ (N : ℝ)/Real.log (N : ℝ)^A := hf N hNf P z
  have hZ : (∑ k ∈ K, Z k) ≤ (N : ℝ)/Real.log (N : ℝ)^A := ht N hNt ε
  change (∑ k ∈ K, goldbachG11RectangleSiftedMass N (goldbachG11GridLong N ε ρ k)
    (goldbachG11GridShort N ρ k) (P k)) ≤ (∑ k ∈ K, main k)+2*(N : ℝ)/Real.log (N : ℝ)^A
  calc
    _ ≤ ∑ k ∈ K, (main k+E k+Z k) := sum_le_sum hpoint
    _ = (∑ k ∈ K, main k)+(∑ k ∈ K,E k)+(∑ k ∈ K,Z k) := by simp only [sum_add_distrib]
    _ ≤ (∑ k ∈ K, main k)+(N : ℝ)/Real.log (N : ℝ)^A+(N : ℝ)/Real.log (N : ℝ)^A :=
      add_le_add (add_le_add (le_refl _) hE) hZ
    _ = _ := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
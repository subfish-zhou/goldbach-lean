import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedOutput

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
namespace G12ClippedWindow

/-- Full ordinary Rosser support, including d=1; no depth or weight modification. -/
theorem output_upperErrSum_le {N : ℕ} {ε : ℝ} {g L U : ℕ → ℝ}
    (hEven : Even N) (h : Admissible N ε g L U) (Z : ℝ)
    (D Q : ℕ) (hDQ : D ≤ Q+1) :
    let S := outputSieve N hEven g L U ε h Z (mass N g L U)
    let P := goldbachB10ProdPrimes N Z
    LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D) ≤
      ∑ d ∈ goldbachG11LinkedModuli N Q, |commonResidual N g L U d| := by
  let S := outputSieve N hEven g L U ε h Z (mass N g L U)
  let P := goldbachB10ProdPrimes N Z
  have hsub : (P.divisors.filter (fun d => d < D)) ⊆ goldbachG11LinkedModuli N Q := by
    intro d hd
    obtain ⟨hdP,hdD⟩ := mem_filter.mp hd
    have hdvd := (Nat.mem_divisors.mp hdP).1
    have hdsq := Squarefree.squarefree_of_dvd hdvd (goldbachB10ProdPrimes_squarefree N Z)
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hdsq.ne_zero
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hd1,by omega⟩,hdsq,
      (goldbachB10_dvd_prodPrimes_coprime_N hdvd).symm⟩
  change (∑ d ∈ P.divisors.filter (fun d => d < D),
    |LinearSieve.upperRosserWeight P D d| * |S.rem d|) ≤ _
  calc
    _ ≤ ∑ d ∈ P.divisors.filter (fun d => d < D), |commonResidual N g L U d| := by
      apply sum_le_sum
      intro d hd
      have hdvd := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
      change |LinearSieve.upperRosserWeight P D d| *
        |(outputSieve N hEven g L U ε h Z (mass N g L U)).rem d| ≤ _
      rw [outputSieve_rem hEven h Z hdvd]
      exact mul_le_of_le_one_left (abs_nonneg _) (LinearSieve.abs_upperRosserWeight_le_one P D d)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => abs_nonneg _)

/-- The density theorem sees exactly the inherited product and multiplicative density. -/
theorem siftedMass_le_rosserFactor (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, ∀ (N : ℕ) (hEven : Even N) (g L U : ℕ → ℝ) (ε : ℝ)
      (h : Admissible N ε g L U) (Z Δ s : ℝ),
      z₀ ≤ Z → 2 ≤ Z → 0 < Δ → s = Real.log Δ/Real.log Z →
      3/2 ≤ s → s ≤ 4 →
      let X := mass N g L U
      let S := outputSieve N hEven g L U ε h Z X
      let P := goldbachB10ProdPrimes N Z
      siftedMass N g L U Z ≤
        X*(jurkatRichertUpperLinearSieveFactor s+ρ)*goldbachB10PrimeProduct N Z +
        LinearSieve.upperErrSum S (Nat.floor Δ+1)
          (LinearSieve.upperRosserWeight P (Nat.floor Δ+1)) := by
  obtain ⟨K,hK,hlocal⟩ := exists_goldbachB10BoundingSieve_dimensionOneLocalProductBound
  have hdensity : DimensionOneUpperRosserDensityFundamentalLemma :=
    MathlibNt.SieveTheory.dimensionOneUpperRosserDensityFundamentalLemma_of_suzuki_allDepth
      jr1965Section13HatLayers jr1965Section13HatSourceContract
      (show MathlibNt.SieveTheory.SuzukiClaim145SourceParameters (16 : ℝ) (1/2 : ℝ) (7 : ℝ) by
        constructor <;> norm_num)
  obtain ⟨z₀,hz₀⟩ := hdensity K ρ hK hρ
  refine ⟨z₀,?_⟩
  intro N hEven g L U ε h Z Δ s hz hZ hΔ hs hslo hshi
  let X := mass N g L U
  let S := outputSieve N hEven g L U ε h Z X
  let P := goldbachB10ProdPrimes N Z
  let D := Nat.floor Δ+1
  have hcert := goldbachG12Linked_upperRosserCertificate (N := N) hZ hΔ hs hslo
  have hprimeCut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ Z := by
    intro p hp
    have hp' : p ∈ P.primeFactors := hp
    have hprime := Nat.prime_of_mem_primeFactors hp'
    have hpdvd := (Nat.mem_primeFactors_of_ne_zero (goldbachB10ProdPrimes_ne_zero N Z)).mp hp' |>.2
    exact (prime_dvd_goldbachB10ProdPrimes_lt hprime hpdvd).le
  have hl : HasDimensionOneLocalProductBound S K := hlocal N hEven 0 0 0 Z X
  have hmain := hz₀ S Z Δ s hz hZ hΔ hl hprimeCut hs hslo hshi
  have heuler : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S = goldbachB10PrimeProduct N Z :=
    (goldbachB10PrimeProduct_eq_sieveProductPrimeFactors N hEven 0 0 0 Z X).symm
  rw [heuler] at hmain
  have hf := LinearSieve.siftedSum_le_mainSum_add_upperErrSum_upperRosser (S := S) D hcert
  change (outputSieve N hEven g L U ε h Z X).siftedSum ≤ _ at hf
  rw [outputSieve_siftedSum] at hf
  have hmx := mul_le_mul_of_nonneg_left hmain (mass_nonneg h)
  change siftedMass N g L U Z ≤
    X*(jurkatRichertUpperLinearSieveFactor s+ρ)*goldbachB10PrimeProduct N Z +
      LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D)
  change siftedMass N g L U Z ≤ X*S.mainSum (LinearSieve.upperRosserWeight P D) +
    LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D) at hf
  change X*S.mainSum (LinearSieve.upperRosserWeight P D) ≤
    X*((jurkatRichertUpperLinearSieveFactor s+ρ)*goldbachB10PrimeProduct N Z) at hmx
  nlinarith only [hf,hmx]

/-- Actual ungated output count with common source mass and fully paid distribution.
The witnesses precede all long weights, endpoints, and epsilon. -/
theorem primeOutput_le_paidRosser (A ρ : ℝ) (hA : 0 < A) (hρ : 0 < ρ) :
    ∃ B C z₀ : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (_hEven : Even N) (g L U : ℕ → ℝ) (ε Z Δ s : ℝ),
      Admissible N ε g L U → z₀ ≤ Z → 2 ≤ Z → 0 < Δ →
      s = Real.log Δ/Real.log Z → 3/2 ≤ s → s ≤ 4 →
      Δ ≤ Real.sqrt N / Real.log (N : ℝ)^B →
      primeOutput N g L U ≤
        400*mass N g L U*(jurkatRichertUpperLinearSieveFactor s+ρ)*goldbachB10PrimeProduct N Z +
          400*C*N/Real.log (N : ℝ)^A + 8000*(Nat.ceil Z : ℝ) := by
  obtain ⟨B,C,hB,hC,K,hK,hdist⟩ := commonResidual_log_saving A hA
  obtain ⟨z₀,hupper⟩ := siftedMass_le_rosserFactor ρ hρ
  refine ⟨B,C,z₀,hB,hC,K,hK,?_⟩
  intro N hN hEven g L U ε Z Δ s h hz hZ hΔ hs hslo hshi hlevel
  have hQ : (Nat.floor Δ : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ)^B :=
    (Nat.floor_le hΔ.le).trans hlevel
  have he := (output_upperErrSum_le hEven h Z (Nat.floor Δ+1) (Nat.floor Δ) le_rfl).trans
    (hdist N hN g L U ε (Nat.floor Δ) h hQ)
  have hu := hupper N hEven g L U ε h Z Δ s hz hZ hΔ hs hslo hshi
  have hg := primeOutput_le_sifted (show 2 ≤ N by omega) h Z
  dsimp only at he hu
  ring_nf at he hu hg ⊢
  linarith only [he,hu,hg]

end G12ClippedWindow

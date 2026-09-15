import OriginalC2
import MathlibNt.SieveTheory.LiLiuFouvryG9ReducedWeights
import MathlibNt.SieveTheory.LiLiuFouvryG9WFLevel

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace OriginalU8

def sifted (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (P : Finset ℕ) : ℝ :=
  weightedSequenceSifted (products (labels N ρ k) ×ˢ primeSupport N ρ k)
    (fun p => ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs)
    (fun p => alpha (labels N ρ k) p.1*beta N p.2) P

def center (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (d : ℕ) : ℝ :=
  g9IntegerFibreCenter (products (labels N ρ k)) (primeSupport N ρ k)
    (alpha (labels N ρ k)) (beta N) d

def discrepancy (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (d : ℕ) : ℝ :=
  bilinearDiscrepancy (products (labels N ρ k)) (primeSupport N ρ k)
    (alpha (labels N ρ k)) (beta N) N d

def exceptional (N : ℕ) (ρ δ : ℝ) (k : ℕ × ℕ × ℕ) (P : Finset ℕ)
    (η z : ℝ) (t : List ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 ⌊level N ρ δ k⌋₊).filter (fun d => ¬ d ∣ P.prod id),
    externalTerm true P (externalInternalLevel (level N ρ δ k) η) η z t d *
      discrepancy N ρ k d

/-- The external upper sieve retains the exact coprime center and signed divisors. -/
theorem weighted_upper (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {D η z : ℝ}
    (hD : 2 ≤ D) (hη : 0 < η) (hηu : η < 1/8)
    (hcut : ∀ p ∈ P, (p : ℝ) < z) :
    sifted N ρ k P ≤
      (∑ t ∈ externalTags true P D η z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D η z t d * center N ρ k d) +
      (∑ t ∈ externalTags true P D η z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D η z t d * discrepancy N ρ k d) := by
  let U := products (labels N ρ k)
  let V := primeSupport N ρ k
  let α := alpha (labels N ρ k)
  let β := beta N
  let a := fun p : ℕ × ℕ => ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs
  let w := fun p : ℕ × ℕ => α p.1*β p.2
  have hw : ∀ p ∈ U ×ˢ V, 0 ≤ w p := by
    intro p _
    apply mul_nonneg (alpha_nonneg _ _)
    dsimp [β,beta,primeSWBeta]
    split_ifs <;> norm_num
  have hc := externalFamily_weighted_sequence_sieve_centered P hP hD hη hηu hcut
    (U ×ˢ V) a w hw (g9IntegerFibreCenter U V α β)
  have heq : ∀ d, weightedDivCount (U ×ˢ V) a w d-g9IntegerFibreCenter U V α β d =
      bilinearDiscrepancy U V α β N d :=
    fun d => g9IntegerFibre_centered_eq U V α β N d
  simp only [heq] at hc
  exact hc

/-- Exact transport: prime-supported full weights are NOT squarefree-masked.
The non-primorial exceptional sum is present, with its sign unchanged. -/
theorem primorial_error_eq (N : ℕ) (ρ δ : ℝ) (k : ℕ × ℕ × ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPN : ∀ p ∈ P, p.Coprime N)
    {η z : ℝ} (hQ : 0 ≤ level N ρ δ k)
    (hD : 2 ≤ externalInternalLevel (level N ρ δ k) η)
    (hη : 0 < η) (hηu : η < 1/8) (t : List ℕ)
    (ht : t ∈ externalTags true P (externalInternalLevel (level N ρ δ k) η) η z) :
    (∑ d ∈ (P.prod id).divisors,
      externalTerm true P (externalInternalLevel (level N ρ δ k) η) η z t d *
        discrepancy N ρ k d) =
      error N ρ δ k (fun d => externalTerm true P
        (externalInternalLevel (level N ρ δ k) η) η z t d) -
        exceptional N ρ δ k P η z t := by
  have h := externalTerm_full_sum_split true P hP z hD hη hηu t ht
    (discrepancy N ρ k)
  rw [externalInternalLevel_level hQ hη hηu] at h
  have he := externalTerm_full_eq_signedError true P
    (externalInternalLevel (level N ρ δ k) η) η z t N hPN
    (products (labels N ρ k)) (primeSupport N ρ k)
    (alpha (labels N ρ k)) (beta N) (level N ρ δ k)
  change (∑ d ∈ Icc 1 ⌊level N ρ δ k⌋₊,
    externalTerm true P (externalInternalLevel (level N ρ δ k) η) η z t d *
      discrepancy N ρ k d) = error N ρ δ k _ at he
  change _ = _ + exceptional N ρ δ k P η z t at h
  rw [he] at h
  linarith

/-- Real external-family consumer: T precedes P, eta, z, every tag and its signed weight.
Only the C2 error is paid here; density and exceptional/low-output payment are separate. -/
theorem sieve_uniform (A : ℕ) {e ε δ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 100/1327)
    (hεδ : ε < δ) (hδ : δ ≤ 1/2) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : ℕ × ℕ × ℕ,
      Occupied N e ρ k → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      ∀ η z : ℝ, 0 < η → η < 1/8 → (∀ p ∈ P, (p : ℝ) < z) →
      0 ≤ level N ρ δ k → 2 ≤ externalInternalLevel (level N ρ δ k) η →
      let D := externalInternalLevel (level N ρ δ k) η
      let S := externalTags true P D η z
      let x := 4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1)
      sifted N ρ k P ≤
        (∑ t ∈ S, ∑ d ∈ (P.prod id).divisors,
          externalTerm true P D η z t d * center N ρ k d) +
        (S.card : ℝ)*(x/Real.log x^A) -
        ∑ t ∈ S, exceptional N ρ δ k P η z t := by
  obtain ⟨N₀,hC2⟩ := error_uniform 1 A he he1 hε hεa hεδ hδ
  refine ⟨N₀,?_⟩
  intro N hN ρ hρ hρu k hne P hP hPN η z hη hηu hcut hQ hD
  dsimp only
  have hu := weighted_upper N ρ k P hP hD hη hηu hcut
  have hb : (∑ t ∈ externalTags true P (externalInternalLevel (level N ρ δ k) η) η z,
      ∑ d ∈ (P.prod id).divisors,
        externalTerm true P (externalInternalLevel (level N ρ δ k) η) η z t d *
          discrepancy N ρ k d) ≤
      (∑ _t ∈ externalTags true P (externalInternalLevel (level N ρ δ k) η) η z,
        (4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1))/
          Real.log (4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1))^A) -
      ∑ t ∈ externalTags true P (externalInternalLevel (level N ρ δ k) η) η z,
        exceptional N ρ δ k P η z t := by
    rw [← sum_sub_distrib]
    apply sum_le_sum
    intro t ht
    rw [primorial_error_eq N ρ δ k P hP hPN hQ hD hη hηu t ht]
    apply sub_le_sub_right
    exact (le_abs_self _).trans (hC2 N hN ρ hρ hρu k hne _
      (externalTerm_signedWellFactorable true P z t hQ hD hη hηu ht))
  simp only [sum_const,nsmul_eq_mul] at hb
  linarith

/-- A quantitative exceptional budget, with its finite local majorant explicit.
This hypothesis is not silently identified with density or asymptotic payment. -/
theorem exceptional_budget (N : ℕ) (ρ δ : ℝ) (k : ℕ × ℕ × ℕ) (P : Finset ℕ)
    {η z H : ℝ} (hD : 2 ≤ externalInternalLevel (level N ρ δ k) η)
    (hη : 0 < η) (hηu : η < 1/8) (hH : 0 ≤ H)
    (hr : ∀ d ∈ Icc 1 ⌊level N ρ δ k⌋₊, |discrepancy N ρ k d| ≤ H/d.totient) :
    (∑ t ∈ externalTags true P (externalInternalLevel (level N ρ δ k) η) η z,
      |exceptional N ρ δ k P η z t|) ≤
      ((externalTags true P (externalInternalLevel (level N ρ δ k) η) η z).card : ℝ)*H*
        (4/(externalInternalLevel (level N ρ δ k) η)^(η^2))*
        (1+Real.log (⌊level N ρ δ k⌋₊ : ℕ))^2 :=
  externalUpperFamily_exceptional_remainder_budget P z hD hη hηu _
    (discrepancy N ρ k) H hH hr

/-- The actual internal level gate is paid at a common cutoff for each fixed eta. -/
theorem sieve_fixed_eta (A : ℕ) {e ε δ η : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 100/1327)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : ℕ × ℕ × ℕ,
      Occupied N e ρ k → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      ∀ z : ℝ, (∀ p ∈ P, (p : ℝ) < z) →
      let D := externalInternalLevel (level N ρ δ k) η
      let S := externalTags true P D η z
      let x := 4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1)
      sifted N ρ k P ≤
        (∑ t ∈ S, ∑ d ∈ (P.prod id).divisors,
          externalTerm true P D η z t d * center N ρ k d) +
        (S.card : ℝ)*(x/Real.log x^A) -
        ∑ t ∈ S, exceptional N ρ δ k P η z t := by
  obtain ⟨N₁,hS⟩ := sieve_uniform A he he1 hε hεa hεδ hδ.le
  obtain ⟨N₂,hparams⟩ := parameters he he1 hε hεa hεδ hδ.le
  obtain ⟨N₃,hgate⟩ := g9WF_exists_internal_level_gate
    (show 0 ≤ δ by linarith) hδ hη 1
  refine ⟨max N₁ (max N₂ N₃),?_⟩
  intro N hN ρ hρ hρu k hne P hP hPN z hcut
  have h₂ := (le_max_left N₂ N₃).trans ((le_max_right _ _).trans hN)
  have h₃ := (le_max_right N₂ N₃).trans ((le_max_right _ _).trans hN)
  have hp := hparams N h₂ ρ hρ hρu k hne
  have hg := geometry he hρ hρu hne
  obtain ⟨_,hQ,_,hD,_⟩ := hgate N ((2/3 : ℝ)*ρ^k.1) h₃ hp.2.2.1 hg.2.2.2.2
  exact hS N ((le_max_left _ _).trans hN) ρ hρ hρu k hne P hP hPN η z
    hη hηu hcut (le_trans zero_le_one hQ) hD

end OriginalU8

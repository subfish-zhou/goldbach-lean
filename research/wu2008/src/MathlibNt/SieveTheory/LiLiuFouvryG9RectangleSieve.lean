import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedSieve
import MathlibNt.SieveTheory.LiLiuFouvryG9IntegerFibre

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def fouvryG9RectanglePrimeSupport (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) : Finset ℕ :=
  primeSWInterval ((⌈max (ρ^k.1) ((N : ℝ)^(4/53 : ℝ))⌉ : ℝ)-1)
    ((⌈min (ρ^(k.1+1)) ((N : ℝ)^(1/10 : ℝ))⌉ : ℝ)-1)

def fouvryG9RectangleBeta (N n : ℕ) : ℝ :=
  if n.Coprime N then primeSWBeta n else 0

/-- Sift the actual separated rectangle, retaining the long-label weights. -/
def fouvryG9RectangleSifted (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (P : Finset ℕ) : ℝ :=
  weightedSequenceSifted
    (fouvryG9LongProducts N ρ k ×ˢ fouvryG9RectanglePrimeSupport N ρ k)
    (fun p => ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs)
    (fun p => fouvryG9LongAlpha N ρ k p.1*fouvryG9RectangleBeta N p.2) P

/-- Actual upper sieve with the exact C2 center. Divisor sums here still
have the primorial carrier; transporting them is a separate obligation. -/
theorem fouvryG9Rectangle_weighted_upper (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {D η z : ℝ}
    (hD : 2 ≤ D) (hη : 0 < η) (hηu : η < 1/8)
    (hcut : ∀ p ∈ P, (p : ℝ) < z) :
    let U := fouvryG9LongProducts N ρ k
    let V := fouvryG9RectanglePrimeSupport N ρ k
    let α := fouvryG9LongAlpha N ρ k
    let β := fouvryG9RectangleBeta N
    fouvryG9RectangleSifted N ρ k P ≤
      (∑ t ∈ externalTags true P D η z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D η z t d * g9IntegerFibreCenter U V α β d) +
      (∑ t ∈ externalTags true P D η z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D η z t d * bilinearDiscrepancy U V α β N d) := by
  dsimp only
  let U := fouvryG9LongProducts N ρ k
  let V := fouvryG9RectanglePrimeSupport N ρ k
  let α := fouvryG9LongAlpha N ρ k
  let β := fouvryG9RectangleBeta N
  let a := fun p : ℕ × ℕ => ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs
  let w := fun p : ℕ × ℕ => α p.1*β p.2
  have hw : ∀ p ∈ U ×ˢ V, 0 ≤ w p := by
    intro p _
    apply mul_nonneg (fouvryG9LongAlpha_nonneg N ρ k p.1)
    dsimp [β, fouvryG9RectangleBeta, primeSWBeta]
    split_ifs <;> norm_num
  have hc := externalFamily_weighted_sequence_sieve_centered P hP hD hη hηu hcut
    (U ×ˢ V) a w hw (g9IntegerFibreCenter U V α β)
  have heq : ∀ d, weightedDivCount (U ×ˢ V) a w d-g9IntegerFibreCenter U V α β d =
      bilinearDiscrepancy U V α β N d :=
    fun d => g9IntegerFibre_centered_eq U V α β N d
  simp only [heq] at hc
  exact hc

/-- The full reduced sum on this very same rectangle is the previously
proved actual G9 error, not a substitute discrepancy. -/
theorem fouvryG9Rectangle_full_error_eq (N : ℕ) (ρ δ : ℝ) (k : ℕ × ℕ × ℕ)
    (c : ℕ → ℝ) :
    signedError (fouvryG9LongProducts N ρ k) (fouvryG9RectanglePrimeSupport N ρ k)
      (Ioc 0 ⌊(N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))⌋₊)
      (fouvryG9LongAlpha N ρ k) (fouvryG9RectangleBeta N) c N =
        fouvryG9RectangleError N ρ δ k c := rfl

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

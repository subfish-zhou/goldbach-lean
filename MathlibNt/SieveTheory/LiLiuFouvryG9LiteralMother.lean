import MathlibNt.SieveTheory.LiLiuFouvryG9SmallOutputPrime
import MathlibNt.SieveTheory.LiLiuGoldbachBuchstab

noncomputable section
open Finset
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Integer absolute difference equals the original natural output on the mother,
not on arbitrary overhanging rectangles. -/
theorem fouvryG9Mother_output_eq {N : ℕ} {e : ℝ} {a : Σ _rs : ℕ × ℕ, ℕ}
    (ha : a ∈ goldbachB9LowPositivePrefixAtoms N e) :
    (((N : ℤ)-((a.1.2*a.2 : ℕ) : ℤ)*a.1.1).natAbs) = goldbachPi10Output N a := by
  have hlt : (a.1.1*a.1.2)*a.2 < N := by
    exact_mod_cast (goldbachB9LowPositivePrefixAtoms_product_window ha).2.2
  have hi : (N : ℤ)-((a.1.2*a.2 : ℕ) : ℤ)*a.1.1 = (goldbachPi10Output N a : ℤ) := by
    unfold goldbachPi10Output goldbachC10Prod
    rw [Nat.cast_sub hlt.le]
    push_cast
    ring
  rw [hi]
  simp

/-- Identical strict prime carriers in the original literal sieve and the new rectangles. -/
theorem fouvryG9SievePrimes_eq_siftingPrimes (N : ℕ) (z : ℝ) :
    fouvryG9SievePrimes N z = siftingPrimes N z := by
  ext p
  rw [fouvryG9SievePrimes_mem,mem_siftingPrimes]
  constructor
  · rintro ⟨hp,hc,hz⟩
    exact ⟨hp,hz,hp.coprime_iff_not_dvd.mp hc⟩
  · rintro ⟨hp,hz,hn⟩
    exact ⟨hp,hp.coprime_iff_not_dvd.mpr hn,hz⟩

/-- Exact literal-H identification, with the natural output and original labels retained. -/
theorem fouvryG9MotherSifted_eq_original (N : ℕ) (e z : ℝ) :
    fouvryG9MotherSifted N e (fouvryG9SievePrimes N z) =
      (goldbachB9LowPositivePrefixSiftedCount N e z : ℝ) := by
  classical
  unfold fouvryG9MotherSifted goldbachB9LowPositivePrefixSiftedCount
  rw [goldbachB9LowPositivePrefixSiftedAtoms_eq_filter,← sum_boole]
  push_cast
  apply sum_congr rfl
  intro a ha
  have ho := fouvryG9Mother_output_eq ha
  push_cast at ho
  rw [ho]
  have hp : literalHPoint N 1 z (goldbachPi10Output N a) ↔
      (goldbachPi10Output N a).Coprime ((fouvryG9SievePrimes N z).prod id) := by
    simp only [literalHPoint,one_dvd,true_and]
    rw [survivesSieve_iff_coprime_siftingProduct,← fouvryG9SievePrimes_eq_siftingPrimes,
      Nat.coprime_comm]
  rw [hp]
  split_ifs <;> norm_num

/-- Exact prime-output count identification; no small outputs are silently removed. -/
theorem fouvryG9MotherPrimeOutput_eq_original (N : ℕ) (e : ℝ) :
    fouvryG9MotherPrimeOutput N e =
      ((goldbachB9LowPositivePrefixPrimeAtoms N e).card : ℝ) := by
  classical
  unfold fouvryG9MotherPrimeOutput goldbachB9LowPositivePrefixPrimeAtoms
  rw [← sum_boole]
  apply sum_congr rfl
  intro a ha
  rw [fouvryG9Mother_output_eq ha]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

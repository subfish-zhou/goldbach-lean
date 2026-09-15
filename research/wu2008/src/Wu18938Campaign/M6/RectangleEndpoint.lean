import Wu18938Campaign.M6.Endpoint
import U8Geometry

noncomputable section
open Finset
open scoped Classical

namespace Wu18938Campaign.M6
open U8Literal

def paperShortPrimeSupport (N : ℕ) (ρ : ℝ) (k : Key) : Finset ℕ :=
  (range (N + 1)).filter fun n =>
    ρ ^ k.1 ≤ (n : ℝ) ∧ (N : ℝ) ^ originalAlpha ≤ (n : ℝ) ∧
      (n : ℝ) < ρ ^ (k.1 + 1) ∧ (n : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)

theorem shortPrimeSupport_subset_paper {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ}
    (hρ : 1 < ρ) (k : Key) :
    shortPrimeSupport N ρ k ⊆ paperShortPrimeSupport N ρ k := by
  intro n hn
  obtain ⟨hlo, hα, hgrid, hcut⟩ := (mem_shortPrimeSupport hN hρ k n).mp hn
  have hroot : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ N by exact_mod_cast hN) (by norm_num : (1 / 10 : ℝ) ≤ 1)
  have hnN : n ≤ N := by exact_mod_cast hcut.le.trans hroot
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), hlo, hα, hgrid, hcut.le⟩

theorem paperShortPrimeSupport_mem_of_prime {N n : ℕ} (hN : 1 ≤ N) {ρ : ℝ}
    (hρ : 1 < ρ) (k : Key) (hp : n.Prime) (hc : n.Coprime N) :
    n ∈ paperShortPrimeSupport N ρ k ↔ n ∈ shortPrimeSupport N ρ k := by
  constructor
  · intro hn
    obtain ⟨_, hlo, hα, hgrid, hcut⟩ := mem_filter.mp hn
    exact (mem_shortPrimeSupport hN hρ k n).mpr
      ⟨hlo, hα, hgrid, (prime_le_tenthRoot_iff_lt hp hc).mp hcut⟩
  · intro hn
    exact shortPrimeSupport_subset_paper hN hρ k hn

theorem paperShortPrimeSupport_beta_sum {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ}
    (hρ : 1 < ρ) (k : Key) (F : ℕ → ℝ) :
    (∑ n ∈ paperShortPrimeSupport N ρ k, rectangleBeta N n * F n) =
      ∑ n ∈ shortPrimeSupport N ρ k, rectangleBeta N n * F n := by
  symm
  apply sum_subset (shortPrimeSupport_subset_paper hN hρ k)
  intro n hn hnot
  by_cases hc : n.Coprime N
  · by_cases hp : n.Prime
    · exact False.elim (hnot ((paperShortPrimeSupport_mem_of_prime hN hρ k hp hc).mp hn))
    · simp [rectangleBeta, hp]
  · simp [rectangleBeta, hc]

def paperRectangleSifted (N : ℕ) (ρ : ℝ) (k : Key) (P : Finset ℕ) : ℝ :=
  weightedSequenceSifted (longProducts N ρ k ×ˢ paperShortPrimeSupport N ρ k)
    (fun t => output N t.2 t.1)
    (fun t => longAlpha N ρ k t.1 * rectangleBeta N t.2) P

theorem paperRectangleSifted_eq {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ}
    (hρ : 1 < ρ) (k : Key) (P : Finset ℕ) :
    paperRectangleSifted N ρ k P = rectangleSifted N ρ k P := by
  simp only [paperRectangleSifted, rectangleSifted, weightedSequenceSifted, sum_product]
  apply sum_congr rfl
  intro m _
  simpa only [mul_assoc, mul_left_comm] using paperShortPrimeSupport_beta_sum hN hρ k
    (fun n => longAlpha N ρ k m * (if (output N n m).Coprime (P.prod id) then 1 else 0))

end Wu18938Campaign.M6

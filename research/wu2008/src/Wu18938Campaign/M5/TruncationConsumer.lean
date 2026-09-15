import Wu18938Campaign.M5.KernelCorner
import Wu18938Campaign.M5.LiteralCount

noncomputable section

namespace Wu18938Campaign.M5.TruncationConsumer

open Real Set MeasureTheory Filter
open Wu18938Campaign.M5.StrictCorner Wu18938Campaign.M5.KernelCorner
open Wu18938Campaign.M5.LiteralCount
open scoped Topology

theorem original_uniform_count_truncation {ε : ℝ} (hε : 0 < ε) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      0 < width n ∧ width n ≤ 1 / 100 ∧
      (∀ N : ℕ, 1 ≤ N →
        countA N (width n) + countB N (width n) ≤ upsilon6 N) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ min (width n) (1 / 100) →
        2 * (25 / 206 : ℝ) + (1 / 2 - 2 * (25 / 206) - width n) < 1 / 2 ∧
        2 * (3 * (100 / 1327 : ℝ) / 2) +
          (1 / 2 - 3 * (100 / 1327) - width n) < 1 / 2 ∧
        2 * (25 / 206 : ℝ) +
          (1 / 2 - 2 * (25 / 206) - width n) ≤ 1 / 2 - δ ∧
        2 * (3 * (100 / 1327 : ℝ) / 2) +
          (1 / 2 - 3 * (100 / 1327) - width n) ≤ 1 / 2 - δ ∧
        ∀ p : ℝ → ℝ, Measurable p → (∀ s ∈ Icc (1 : ℝ) 5, |p s| ≤ 10) →
          |originalMass (kernel δ p) 0 -
            originalMass (kernel δ p) (width n)| < ε := by
  obtain ⟨η0, hη0, hη0hi, hmass⟩ := original_kernel_uniform_limit hε
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp (width_tendsto.eventually (gt_mem_nhds hη0))
  refine ⟨n0, ?_⟩
  intro n hn
  have hw := hn0 n hn
  refine ⟨width_pos n, hw.le.trans hη0hi,
    fun N hN => original_trimmed_le hN (width_pos n).le, ?_⟩
  intro δ hδ hδhi
  obtain ⟨hδw, hδ100⟩ := le_min_iff.mp hδhi
  have hs := original_strict_slack (width_pos n) hδw
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2,
    fun p hp hb => hmass (width n) (width_pos n) hw δ hδ hδ100 p hp hb⟩

end Wu18938Campaign.M5.TruncationConsumer

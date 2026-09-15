import MathlibNt.Wu2004MeanValue.ManuscriptPairs
import MathlibNt.Wu2004MeanValue.RealClosed
import MathlibNt.Wu2004MeanValue.RealOpen
import MathlibNt.Wu2004MeanValue.RealSieveSupport
import MathlibNt.Wu2004MeanValue.CutoffSeparation

/-! Common-X sequence remainders on the literal sieve-divisor support.
The actual coefficient is one on the literal prime carrier. Uniform power
separation removes the common-factor correction exactly, and the closed
tail's lower atom and open block's upper atom have already been paid. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

theorem tail_sequence_remainder_weighted (A c τ η : ℝ)
    (hA : 0 < A) (hc : 0 < c) (hτ : 1 / 3 < τ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℝ,
      ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ D : ℝ, 0 ≤ D → D ≤ Real.sqrt N / Real.log N ^ B →
      (∑ d ∈ sieveDivisors N D, wuModulusWeight d * |tailRemainder N c τ η d|) ≤
        C * N / Real.log N ^ A := by
  obtain ⟨B, C, hB, hC, X₀, hbound⟩ :=
    manuscript_tail_closed_weighted A 1 η hA (by norm_num) hη hη1
  obtain ⟨X₁, _, hsep⟩ := tail_real_sieve_cutoff_separation c τ hc (by linarith)
  refine ⟨B, C, hB, hC, max X₀ X₁, ?_⟩
  intro N hN D hD0 hD
  have hN₀ : X₀ ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hN₁ : X₁ ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hcut : (⌊D⌋₊ : ℝ) ≤ Real.sqrt N / Real.log N ^ B :=
    (Nat.floor_le hD0).trans hD
  have hsource : ∀ m ∈ tailSource N c τ, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt N := by
    intro m hm
    have h := mem_tailSource.mp hm
    exact ⟨h.1.one_le, h.2.2.2⟩
  have hlarge : ∀ m ∈ tailSource N c τ, Real.sqrt D < (m : ℝ) := by
    intro m hm
    exact (hsep N hN₁ B hB.le D hD).trans_lt (mem_tailSource.mp hm).2.2.1
  have hidentity (d : ℕ) (hd : d ∈ sieveDivisors N D) :
      tailRemainder N c τ η d =
        actualClosedErrorSum (tailSource N c τ) (fun _ => 1)
          (fun _ => η * N) (fun _ => N) d N := by
    change indexedRemainder true (tailSource N c τ) (fun _ => η * N)
      (fun _ => N) N d = _
    rw [indexedRemainder_eq_error_on_sieve true (tailSource N c τ)
      (fun _ => η * N) (fun _ => N)
      (sieveDivisors_subset_sieveModuli N D hd)
      (fun m hm => ⟨(mem_tailSource.mp hm).1, (hlarge m hm).le,
        Nat.cast_nonneg N, le_rfl⟩), intervalErrorSum_closed]
  calc
    _ = ∑ d ∈ sieveDivisors N D, wuModulusWeight d *
        |actualClosedErrorSum (tailSource N c τ) (fun _ => 1)
          (fun _ => η * N) (fun _ => N) d N| := by
      exact sum_congr rfl (fun d hd => by rw [hidentity d hd])
    _ ≤ ∑ d ∈ (Icc 1 ⌊D⌋₊).filter (fun d => N.Coprime d), wuModulusWeight d *
        |actualClosedErrorSum (tailSource N c τ) (fun _ => 1)
          (fun _ => η * N) (fun _ => N) d N| := by
      apply sum_le_sum_of_subset_of_nonneg (sieveDivisors_subset_coprime N D)
      intro d _ _
      exact mul_nonneg (wuModulusWeight_nonneg d) (abs_nonneg _)
    _ ≤ _ := hbound N hN₀ ⌊D⌋₊ hcut (tailSource N c τ) (fun _ => 1)
      hsource (by intros; norm_num)

theorem tail_sequence_remainder_muSquare (A c τ η : ℝ)
    (hA : 0 < A) (hc : 0 < c) (hτ : 1 / 3 < τ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℝ,
      ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ D : ℝ, 0 ≤ D → D ≤ Real.sqrt N / Real.log N ^ B →
      (∑ d ∈ sieveDivisors N D, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
        |tailRemainder N c τ η d|) ≤ C * N / Real.log N ^ A := by
  obtain ⟨B, C, hB, hC, N₀, hbound⟩ :=
    tail_sequence_remainder_weighted A c τ η hA hc hτ hη hη1
  refine ⟨B, C, hB, hC, N₀, ?_⟩
  intro N hN D hD0 hD
  exact (muSquare_sum_le_wu _ _ (fun _ _ => abs_nonneg _)).trans
    (hbound N hN D hD0 hD)

theorem block_sequence_remainder_weighted (A a : ℝ)
    (hA : 0 < A) (ha : 3 / 2 < a) (ha2 : a < 2) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ H₀ : ℝ,
      ∀ H : ℝ, H₀ ≤ H → ∀ (N : ℕ) (η : ℝ), η ≤ 1 →
      ∀ D : ℝ, 0 ≤ D → D ≤ Real.sqrt (2 * H) / Real.log (2 * H) ^ B →
      (∑ d ∈ sieveDivisors N D, wuModulusWeight d * |blockRemainder H N a η d|) ≤
        C * (2 * H) / Real.log (2 * H) ^ A := by
  obtain ⟨B, C, hB, hC, X₀, hbound⟩ :=
    manuscript_block_open_weighted A 1 hA (by norm_num)
  have hτ := (block_source_exponent_range ha ha2).1
  obtain ⟨X₁, hX₁, hsep⟩ :=
    block_real_sieve_cutoff_separation ((a - 1) / a) (by linarith)
  refine ⟨B, C, hB, hC, max X₀ X₁, ?_⟩
  intro H hH N η hη D hD0 hD
  have hH₁ : X₁ ≤ H := (le_max_right _ _).trans hH
  have hHX : X₀ ≤ H := (le_max_left _ _).trans hH
  have hH₀ : X₀ ≤ 2 * H := by linarith
  have hcut : (⌊D⌋₊ : ℝ) ≤ Real.sqrt (2 * H) / Real.log (2 * H) ^ B :=
    (Nat.floor_le hD0).trans hD
  have hlarge : ∀ m ∈ blockSource H N a η, Real.sqrt D < (m : ℝ) := by
    intro m hm
    exact (hsep H hH₁ B hB.le D hD).trans_lt (mem_blockSource.mp hm).2.2.1
  have hidentity (d : ℕ) (hd : d ∈ sieveDivisors N D) :
      blockRemainder H N a η d =
        actualOpenErrorSum (blockSource H N a η) (fun _ => 1)
          (blockLower H) (blockUpper H N a η) d N := by
    change indexedRemainder false (blockSource H N a η)
      (blockLower H) (blockUpper H N a η) N d = _
    rw [indexedRemainder_eq_error_on_sieve false (blockSource H N a η)
      (blockLower H) (blockUpper H N a η) (sieveDivisors_subset_sieveModuli N D hd)
      (fun m hm => ⟨(mem_blockSource.mp hm).1, (hlarge m hm).le,
        blockSource_upper_domain hm hη⟩), intervalErrorSum_open]
  calc
    _ = ∑ d ∈ sieveDivisors N D, wuModulusWeight d *
        |actualOpenErrorSum (blockSource H N a η) (fun _ => 1)
          (blockLower H) (blockUpper H N a η) d N| := by
      exact sum_congr rfl (fun d hd => by rw [hidentity d hd])
    _ ≤ ∑ d ∈ (Icc 1 ⌊D⌋₊).filter (fun d => N.Coprime d), wuModulusWeight d *
        |actualOpenErrorSum (blockSource H N a η) (fun _ => 1)
          (blockLower H) (blockUpper H N a η) d N| := by
      apply sum_le_sum_of_subset_of_nonneg (sieveDivisors_subset_coprime N D)
      intro d _ _
      exact mul_nonneg (wuModulusWeight_nonneg d) (abs_nonneg _)
    _ ≤ _ := hbound H hH₀ N a η ⌊D⌋₊ hcut (blockSource H N a η) (fun _ => 1)
      (fun m hm => ⟨(mem_blockSource.mp hm).1, (mem_blockSource.mp hm).2.2.2.2⟩)
      (by intros; norm_num)

theorem block_sequence_remainder_muSquare (A a : ℝ)
    (hA : 0 < A) (ha : 3 / 2 < a) (ha2 : a < 2) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ H₀ : ℝ,
      ∀ H : ℝ, H₀ ≤ H → ∀ (N : ℕ) (η : ℝ), η ≤ 1 →
      ∀ D : ℝ, 0 ≤ D → D ≤ Real.sqrt (2 * H) / Real.log (2 * H) ^ B →
      (∑ d ∈ sieveDivisors N D, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
        |blockRemainder H N a η d|) ≤ C * (2 * H) / Real.log (2 * H) ^ A := by
  obtain ⟨B, C, hB, hC, H₀, hbound⟩ := block_sequence_remainder_weighted A a hA ha ha2
  refine ⟨B, C, hB, hC, H₀, ?_⟩
  intro H hH N η hη D hD0 hD
  exact (muSquare_sum_le_wu _ _ (fun _ _ => abs_nonneg _)).trans
    (hbound H hH N η hη D hD0 hD)

end
end Wu2004MeanValue

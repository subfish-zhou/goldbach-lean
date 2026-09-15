import MathlibNt.Wu2004MeanValue.IndexedPairs
import MathlibNt.Wu2004MeanValue.EndpointConsumers

/-! Literal source carriers and indexed sequences of the frozen manuscript,
lines 153--155 and 241--256. No image-cardinality convention is used. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

def tailSource (N : ℕ) (c τ : ℝ) : Finset ℕ :=
  (range (⌊Real.sqrt N⌋₊ + 1)).filter
    (fun m => m.Prime ∧ m.Coprime N ∧ c * (N : ℝ) ^ τ < m)

theorem mem_tailSource {N m : ℕ} {c τ : ℝ} :
    m ∈ tailSource N c τ ↔
      m.Prime ∧ m.Coprime N ∧ c * (N : ℝ) ^ τ < m ∧ (m : ℝ) ≤ Real.sqrt N := by
  simp only [tailSource, mem_filter, mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff (Real.sqrt_nonneg _)]
  tauto

def blockSource (H : ℝ) (N : ℕ) (a η : ℝ) : Finset ℕ :=
  (range (⌊Real.sqrt (2 * H)⌋₊ + 1)).filter
    (fun m => m.Prime ∧ m.Coprime N ∧ H ^ ((a - 1) / a) < m ∧
      blockLower H m < blockUpper H N a η m)

theorem mem_blockSource {H : ℝ} {N m : ℕ} {a η : ℝ} :
    m ∈ blockSource H N a η ↔
      m.Prime ∧ m.Coprime N ∧ H ^ ((a - 1) / a) < m ∧
        (m : ℝ) ≤ Real.sqrt (2 * H) ∧ blockLower H m < blockUpper H N a η m := by
  simp only [blockSource, mem_filter, mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff (Real.sqrt_nonneg _)]
  tauto

theorem blockSource_upper_domain {H : ℝ} {N m : ℕ} {a η : ℝ}
    (hm : m ∈ blockSource H N a η) (hη : η ≤ 1) :
    0 ≤ blockUpper H N a η m ∧ blockUpper H N a η m ≤ N := by
  have h := mem_blockSource.mp hm
  have hlo : 0 ≤ blockLower H m :=
    (sq_nonneg (m : ℝ)).trans (le_max_right _ _)
  refine ⟨hlo.trans h.2.2.2.2.le, ?_⟩
  calc
    blockUpper H N a η m ≤ η * N := min_le_right _ _
    _ ≤ (N : ℝ) := by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg N)

def tailPairs (N : ℕ) (c τ η : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  indexedPrimePairs true (tailSource N c τ) (fun _ => η * N) (fun _ => N)

def blockPairs (H : ℝ) (N : ℕ) (a η : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  indexedPrimePairs false (blockSource H N a η) (blockLower H) (blockUpper H N a η)

theorem mem_tailPairs {N m p : ℕ} {c τ η : ℝ} :
    (⟨m, p⟩ : Σ _ : ℕ, ℕ) ∈ tailPairs N c τ η ↔
      m ∈ tailSource N c τ ∧ p.Prime ∧ η * N ≤ (m : ℝ) * p ∧ (m : ℝ) * p ≤ N := by
  by_cases hm : m ∈ tailSource N c τ
  · simpa only [tailPairs, if_true, and_assoc] using
      (mem_indexedPrimePairs (closed := true) (lo := fun _ => η * N)
        (hi := fun _ => (N : ℝ)) (m := m)
        (p := p) (show 0 ≤ (N : ℝ) by positivity) (mem_tailSource.mp hm).1.pos)
  · simp [tailPairs, indexedPrimePairs, hm]

theorem mem_blockPairs {H : ℝ} {N m p : ℕ} {a η : ℝ} :
    (⟨m, p⟩ : Σ _ : ℕ, ℕ) ∈ blockPairs H N a η ↔
      m ∈ blockSource H N a η ∧ p.Prime ∧
        blockLower H m < (m : ℝ) * p ∧ (m : ℝ) * p < blockUpper H N a η m := by
  by_cases hm : m ∈ blockSource H N a η
  · have h := mem_blockSource.mp hm
    have hhi : 0 ≤ blockUpper H N a η m :=
      ((sq_nonneg (m : ℝ)).trans (le_max_right _ _)).trans h.2.2.2.2.le
    simpa only [blockPairs, Bool.false_eq_true, if_false, and_assoc] using
      (mem_indexedPrimePairs (closed := false) (lo := blockLower H)
        (p := p) hhi h.1.pos)
  · simp [blockPairs, indexedPrimePairs, hm]

theorem tail_pair_product_lt {N : ℕ} {c τ η : ℝ} {t : Σ _ : ℕ, ℕ}
    (ht : t ∈ tailPairs N c τ η) : t.1 * t.2 < N := by
  have h := mem_tailPairs.mp ht
  have hs := mem_tailSource.mp h.1
  have hle : t.1 * t.2 ≤ N := by exact_mod_cast h.2.2.2
  apply lt_of_le_of_ne hle
  intro heq
  have hnot := hs.1.coprime_iff_not_dvd.mp hs.2.1
  exact hnot (heq ▸ dvd_mul_right t.1 t.2)

theorem block_pair_product_lt {H : ℝ} {N : ℕ} {a η : ℝ} {t : Σ _ : ℕ, ℕ}
    (ht : t ∈ blockPairs H N a η) (hη : η ≤ 1) : t.1 * t.2 < N := by
  have h := mem_blockPairs.mp ht
  have hlt := h.2.2.2.trans_le (blockSource_upper_domain h.1 hη).2
  exact_mod_cast hlt

theorem tail_pairValue_pos {N : ℕ} {c τ η : ℝ} {t : Σ _ : ℕ, ℕ}
    (ht : t ∈ tailPairs N c τ η) : 0 < pairValue N t :=
  Nat.sub_pos_of_lt (tail_pair_product_lt ht)

theorem block_pairValue_pos {H : ℝ} {N : ℕ} {a η : ℝ} {t : Σ _ : ℕ, ℕ}
    (ht : t ∈ blockPairs H N a η) (hη : η ≤ 1) : 0 < pairValue N t :=
  Nat.sub_pos_of_lt (block_pair_product_lt ht hη)

theorem tail_pairValue_dvd_iff {N d : ℕ} {c τ η : ℝ} {t : Σ _ : ℕ, ℕ}
    (ht : t ∈ tailPairs N c τ η) :
    d ∣ pairValue N t ↔ t.1 * t.2 ≡ N [MOD d] :=
  pairValue_dvd_iff (tail_pair_product_lt ht).le

theorem block_pairValue_dvd_iff {H : ℝ} {N d : ℕ} {a η : ℝ} {t : Σ _ : ℕ, ℕ}
    (ht : t ∈ blockPairs H N a η) (hη : η ≤ 1) :
    d ∣ pairValue N t ↔ t.1 * t.2 ≡ N [MOD d] :=
  pairValue_dvd_iff (block_pair_product_lt ht hη).le

def tailMass (N : ℕ) (c τ η : ℝ) : ℝ :=
  intervalMass (tailSource N c τ) (fun _ => η * N) (fun _ => N)

def blockMass (H : ℝ) (N : ℕ) (a η : ℝ) : ℝ :=
  intervalMass (blockSource H N a η) (blockLower H) (blockUpper H N a η)

def tailRemainder (N : ℕ) (c τ η : ℝ) (d : ℕ) : ℝ :=
  (indexedDivisibleCount N (tailPairs N c τ η) d : ℝ) - tailMass N c τ η / d.totient

def blockRemainder (H : ℝ) (N : ℕ) (a η : ℝ) (d : ℕ) : ℝ :=
  (indexedDivisibleCount N (blockPairs H N a η) d : ℝ) - blockMass H N a η / d.totient

theorem tail_count_common_main (N d : ℕ) (c τ η : ℝ) (hN : N.Coprime d) :
    (indexedDivisibleCount N (tailPairs N c τ η) d : ℝ) =
      tailMass N c τ η / d.totient +
        actualClosedErrorSum (tailSource N c τ) (fun _ => 1) (fun _ => η * N)
          (fun _ => N) d N -
        (∑ m ∈ tailSource N c τ with m ∣ d,
          (wuLi ((N : ℝ) / m) - wuLi (η * N / m))) / d.totient := by
  simpa only [tailPairs, tailMass, intervalErrorSum_closed] using
    indexedDivisibleCount_common_main true (tailSource N c τ)
      (fun _ => η * N) (fun _ => N) N d hN
      (fun m hm => ⟨(mem_tailSource.mp hm).1, Nat.cast_nonneg N, le_rfl⟩)

theorem block_count_common_main (H : ℝ) (N d : ℕ) (a η : ℝ)
    (hN : N.Coprime d) (hη : η ≤ 1) :
    (indexedDivisibleCount N (blockPairs H N a η) d : ℝ) =
      blockMass H N a η / d.totient +
        actualOpenErrorSum (blockSource H N a η) (fun _ => 1)
          (blockLower H) (blockUpper H N a η) d N -
        (∑ m ∈ blockSource H N a η with m ∣ d,
          (wuLi (blockUpper H N a η m / m) - wuLi (blockLower H m / m))) /
            d.totient := by
  simpa only [blockPairs, blockMass, intervalErrorSum_open] using
    indexedDivisibleCount_common_main false (blockSource H N a η)
      (blockLower H) (blockUpper H N a η) N d hN
      (fun m hm => ⟨(mem_blockSource.mp hm).1, blockSource_upper_domain hm hη⟩)

end
end Wu2004MeanValue

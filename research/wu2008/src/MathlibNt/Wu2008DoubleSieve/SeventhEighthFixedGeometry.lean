import MathlibNt.Wu2008DoubleSieve.SeventhEighthExceptions

/-! The original fixed seventh and eighth domains, without enlarging their
ranges. The seventh lowerS2 filter is u ≤ a, not w ≤ a. -/
namespace Wu2008DoubleSieve.SeventhEighth
open Finset Real

noncomputable def alpha : ℝ := 100 / 1327
noncomputable def beta : ℝ := 25 / 206
noncomputable def sigma : ℝ := 1 / 2 - 3 * alpha
noncomputable def z (N : ℕ) : ℝ := (N : ℝ) ^ alpha
noncomputable def w (N : ℕ) : ℝ := (N : ℝ) ^ beta
noncomputable def u (N : ℕ) : ℝ := (N : ℝ) ^ sigma
noncomputable def v (N : ℕ) : ℝ := (N : ℝ) ^ (1 / 3 : ℝ)

noncomputable def seventhPairs (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (lowerPairs N N (w N) (u N)).filter fun t => u N ≤ t.1

noncomputable def eighthPairs (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (lowerPairs N N (z N) (v N)).filter fun t => (t.1 : ℝ) < v N

noncomputable def physicalT7 (N : ℕ) : Finset NinthLabel := physical N (seventhPairs N)
noncomputable def physicalT8 (N : ℕ) : Finset NinthLabel := physical N (eighthPairs N)

/-- Exact membership includes the original coprimality and finite windows. -/
theorem lowerPairs_data {N : ℕ} {s t : ℝ} {a b : ℕ}
    (h : (a, b) ∈ lowerPairs N N s t) :
    Nat.Prime a ∧ Nat.Prime b ∧ a.Coprime N ∧ b.Coprime N ∧
      s ≤ a ∧ t ≤ b ∧ a < b ∧ a * b ^ 2 < N := by
  obtain ⟨hp, hab, hprod⟩ := mem_filter.mp h
  obtain ⟨ha, hb⟩ := mem_product.mp hp
  obtain ⟨hap, hac, hsa, _⟩ := mem_primeWindow.mp ha
  obtain ⟨hbp, hbc, htb, _⟩ := mem_primeWindow.mp hb
  exact ⟨hap, hbp, hac, hbc, hsa, htb, hab, hprod⟩

theorem seventh_pairDomain {N : ℕ} (hN : 1 ≤ N) :
    PairDomain N alpha (seventhPairs N) := by
  classical
  intro t ht
  obtain ⟨ht, _⟩ := mem_filter.mp ht
  obtain ⟨ha, hb, _, _, hw, _, hab, hg⟩ := lowerPairs_data ht
  refine ⟨ha, hb, ?_, hab, hg⟩
  exact (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    (by norm_num [alpha, beta] : alpha ≤ beta)).trans hw

theorem eighth_pairDomain (N : ℕ) : PairDomain N alpha (eighthPairs N) := by
  classical
  intro t ht
  obtain ⟨ht, _⟩ := mem_filter.mp ht
  obtain ⟨ha, hb, _, _, hz, _, hab, hg⟩ := lowerPairs_data ht
  exact ⟨ha, hb, hz, hab, hg⟩

/-- Symbolic product geometry; only fixed rational algebra is used. -/
theorem cube_geometry {N a b : ℕ} {s t : ℝ} (hN : 1 ≤ N)
    (hsa : (N : ℝ) ^ s ≤ a) (htb : (N : ℝ) ^ t ≤ b)
    (hexp : 1 ≤ s + 3 * t) : N ≤ a * b ^ 3 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : ((N : ℝ) ^ t) ^ (3 : ℕ) ≤ (b : ℝ) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (rpow_nonneg hN0.le _) htb 3
  have heq : (N : ℝ) ^ s * ((N : ℝ) ^ t) ^ (3 : ℕ) =
      (N : ℝ) ^ (s + 3 * t) := by
    rw [← rpow_natCast, ← rpow_mul hN0.le, ← rpow_add hN0]
    congr 1
    ring
  have hp := mul_le_mul hsa hc (by positivity) (by positivity : (0 : ℝ) ≤ a)
  rw [heq] at hp
  have hn : (N : ℝ) ≤ (N : ℝ) ^ (s + 3 * t) := by
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hexp
  exact_mod_cast hn.trans hp

theorem seventh_geometry {N : ℕ} (hN : 1 ≤ N) :
    ∀ t ∈ seventhPairs N, Nat.Prime t.1 ∧ Nat.Prime t.2 ∧ N ≤ t.1 * t.2 ^ 3 := by
  classical
  intro t ht
  obtain ⟨ht, hu⟩ := mem_filter.mp ht
  obtain ⟨ha, hb, _, _, _, hub, _, _⟩ := lowerPairs_data ht
  exact ⟨ha, hb, cube_geometry hN hu hub (by norm_num [sigma, alpha])⟩

theorem eighth_geometry {N : ℕ} (hN : 1 ≤ N) :
    ∀ t ∈ eighthPairs N, Nat.Prime t.1 ∧ Nat.Prime t.2 ∧ N ≤ t.1 * t.2 ^ 3 := by
  classical
  intro t ht
  obtain ⟨ht, _⟩ := mem_filter.mp ht
  obtain ⟨ha, hb, _, _, hz, hv, _, _⟩ := lowerPairs_data ht
  exact ⟨ha, hb, cube_geometry hN hz hv (by norm_num [alpha])⟩

theorem seventh_atoms_card (N : ℕ) :
    ((atoms N (seventhPairs N)).card : ℤ) = lowerS2 N (w N) (u N) :=
  atoms_card N (seventhPairs N)

theorem eighth_atoms_card (N : ℕ) :
    ((atoms N (eighthPairs N)).card : ℤ) = lowerS3 N (z N) (v N) :=
  atoms_card N (eighthPairs N)

/-- The physical labels are (a,b,r), not images under multiplication.
The r = b endpoint is explicitly retained. -/
theorem mem_physicalT7 {N a b r : ℕ} :
    (⟨(a, b), r⟩ : NinthLabel) ∈ physicalT7 N ↔
      (a, b) ∈ lowerPairs N N (w N) (u N) ∧ u N ≤ a ∧
      r < N + 1 ∧ Nat.Prime r ∧ b ≤ r ∧ a * b * r < N ∧
      Nat.Prime (N - a * b * r) := by
  classical
  simp only [physicalT7, physical, seventhPairs, mem_sigma, mem_filter, mem_range]
  tauto

theorem mem_physicalT8 {N a b r : ℕ} :
    (⟨(a, b), r⟩ : NinthLabel) ∈ physicalT8 N ↔
      (a, b) ∈ lowerPairs N N (z N) (v N) ∧ (a : ℝ) < v N ∧
      r < N + 1 ∧ Nat.Prime r ∧ b ≤ r ∧ a * b * r < N ∧
      Nat.Prime (N - a * b * r) := by
  classical
  simp only [physicalT8, physical, eighthPairs, mem_sigma, mem_filter, mem_range]
  tauto

end Wu2008DoubleSieve.SeventhEighth

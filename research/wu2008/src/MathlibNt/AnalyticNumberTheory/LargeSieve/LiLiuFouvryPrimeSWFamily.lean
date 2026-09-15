import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeSWUniform

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open Finset Filter
open scoped Topology
noncomputable section

/-- The real upper endpoint and its natural floor have comparable logarithms. -/
theorem primeSW_floor_log_comparison {x : ℝ} (hx : 3 ≤ x) :
    0 < Real.log (⌊x⌋₊ : ℝ) ∧ Real.log x ≤ 2 * Real.log (⌊x⌋₊ : ℝ) := by
  have hN : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hNr : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < ⌊x⌋₊ := by linarith
  have hxN : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
    have hf := Nat.lt_floor_add_one x
    linarith
  refine ⟨Real.log_pos (by linarith), ?_⟩
  calc
    Real.log x ≤ Real.log (2 * (⌊x⌋₊ : ℝ)) :=
      Real.log_le_log (by linarith) hxN
    _ = Real.log 2 + Real.log (⌊x⌋₊ : ℝ) :=
      Real.log_mul (by norm_num) hNr0.ne'
    _ ≤ _ := by have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hNr; linarith

/-- A simple global interval bound, with no lower-endpoint prime-density input. -/
theorem primeSW_interval_card_bound {T u v : ℝ} (hT : 1 ≤ T) (hv : v ≤ 2 * T)
    {d : ℕ} (hd : 0 < d) (h b : ℕ) :
    |betaCoprimeAPDiscrepancy (primeSWInterval u v) primeSWBeta d h b| ≤ 4 * T := by
  have hcard : (primeSWInterval u v).card ≤ ⌊v⌋₊ := by
    apply (card_le_card (show primeSWInterval u v ⊆ Icc 1 ⌊v⌋₊ from by
      intro n hn
      obtain ⟨hn0, hnv⟩ := mem_Ioc.mp hn
      exact mem_Icc.mpr ⟨by omega, hnv⟩)).trans
    simp
  have hfloor : (⌊v⌋₊ : ℝ) ≤ 2 * T := by
    by_cases hv0 : 0 ≤ v
    · exact (Nat.floor_le hv0).trans hv
    · rw [Nat.floor_of_nonpos (le_of_not_ge hv0), Nat.cast_zero]
      linarith
  have hcardR : ((primeSWInterval u v).card : ℝ) ≤ ⌊v⌋₊ := by exact_mod_cast hcard
  have hbnd := primeSW_discrepancy_le_card (primeSWInterval u v) hd h b
  linarith

/-- All real dyadic prime intervals satisfy the independently sieved SW estimate.
The saving constant is selected before the scale, both endpoints, and all arithmetic data. -/
theorem primeSW_uniform_real (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T u v : ℝ, 1 ≤ T → T ≤ u → u ≤ v → v ≤ 2 * T →
      ∀ d h : ℕ, 0 < d → 0 < h → ∀ b : ℕ, b.Coprime d →
      |betaCoprimeAPDiscrepancy (primeSWInterval u v) primeSWBeta d h b| ≤
        C * T * (fouvryTau 2 h : ℝ) / Real.log (2 * T) ^ B := by
  obtain ⟨c, hc, htail⟩ := primeSW_uniform_eventually B
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp htail
  let M : ℝ := max (N₀ : ℝ) 3
  let C : ℝ := c * 2 ^ (B + 1) + 4 * Real.log (2 * M) ^ B
  have hM3 : 3 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hlogM : 0 < Real.log (2 * M) := Real.log_pos (by linarith)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro T u v hT hTu huv hv d h hd hh b hb
  let t : ℝ := fouvryTau 2 h
  have ht : 1 ≤ t := by
    dsimp [t]
    rw [fouvryTau_two]
    exact_mod_cast Finset.one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd h, by omega⟩⟩
  have ht0 : 0 ≤ t := by linarith
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  have hCtail : c * 2 ^ (B + 1) ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  have hCsmall : 4 * Real.log (2 * M) ^ B ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_left (by positivity)
  change |betaCoprimeAPDiscrepancy (primeSWInterval u v) primeSWBeta d h b| ≤
    C * T * t / Real.log (2 * T) ^ B
  by_cases hlarge : M ≤ T
  · let N : ℕ := ⌊2 * T⌋₊
    have hTN : (N₀ : ℝ) ≤ 2 * T := (le_max_left _ _).trans (by linarith)
    have hN : N₀ ≤ N := Nat.le_floor hTN
    have hu : ⌊u⌋₊ ∈ Icc 2 N := mem_Icc.mpr ⟨Nat.le_floor (by norm_num; linarith),
      Nat.floor_mono (huv.trans hv)⟩
    have hv' : ⌊v⌋₊ ∈ Icc 2 N := mem_Icc.mpr ⟨Nat.le_floor (by norm_num; linarith), Nat.floor_mono hv⟩
    have hraw := hN₀ N hN u v huv hu hv' d h hd hh b hb
    obtain ⟨hLN, hcomp⟩ := primeSW_floor_log_comparison (x := 2 * T) (by linarith)
    have hNreal : (N : ℝ) ≤ 2 * T := Nat.floor_le (by positivity)
    have hp : Real.log (2 * T) ^ B ≤ 2 ^ B * Real.log (N : ℝ) ^ B := by
      simpa only [mul_pow] using pow_le_pow_left₀ hlog.le hcomp B
    apply hraw.trans
    apply (div_le_div_iff₀ (pow_pos hLN B) (pow_pos hlog B)).mpr
    calc
      c * (N : ℝ) * t * Real.log (2 * T) ^ B ≤
          c * (2 * T) * t * (2 ^ B * Real.log (N : ℝ) ^ B) := by
        gcongr
      _ = (c * 2 ^ (B + 1)) * T * t * Real.log (N : ℝ) ^ B := by rw [pow_succ]; ring
      _ ≤ C * T * t * Real.log (N : ℝ) ^ B := by gcongr
  · have hTM : T ≤ M := le_of_lt (lt_of_not_ge hlarge)
    have hlogs : Real.log (2 * T) ^ B ≤ Real.log (2 * M) ^ B := by
      apply pow_le_pow_left₀ hlog.le
      exact Real.log_le_log (by positivity) (by linarith)
    apply (primeSW_interval_card_bound hT hv hd h b).trans
    apply (le_div_iff₀ (pow_pos hlog B)).mpr
    have hpay : 4 * Real.log (2 * T) ^ B ≤ C := (by gcongr :
      4 * Real.log (2 * T) ^ B ≤ 4 * Real.log (2 * M) ^ B).trans hCsmall
    calc
      4 * T * Real.log (2 * T) ^ B = (4 * Real.log (2 * T) ^ B) * T := by ring
      _ ≤ C * T := mul_le_mul_of_nonneg_right hpay hT0.le
      _ ≤ C * T * t := le_mul_of_one_le_right (by dsimp [C]; positivity) ht

/-- The concrete prime-interval family, with fixed divisor order two. -/
theorem primeSW_BetaCoprimeSWFamily {ι : Type*} (T u v : ι → ℝ)
    (hT : ∀ i, 1 ≤ T i) (hTu : ∀ i, T i ≤ u i)
    (huv : ∀ i, u i ≤ v i) (hv : ∀ i, v i ≤ 2 * T i) :
    BetaCoprimeSWFamily 2 T (fun i => primeSWInterval (u i) (v i))
      (fun _ => primeSWBeta) := by
  intro B
  obtain ⟨C, hC, hbound⟩ := primeSW_uniform_real B
  exact ⟨C, hC, fun i => hbound (T i) (u i) (v i) (hT i) (hTu i) (huv i) (hv i)⟩

end
end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

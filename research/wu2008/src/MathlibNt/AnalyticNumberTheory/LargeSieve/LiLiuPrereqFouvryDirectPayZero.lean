import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayZeroSquare

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Uniform payment of the actual joined zero contribution. The constant precedes
all varying data. Neither energy nor mass nor a target-sized envelope is an input. -/
theorem directPayZero_uniform
    (ε ρ η Czero Ccoeff Couter : ℝ)
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hCz : 0 ≤ Czero) (hCc : 0 ≤ Ccoeff) (hCo : 0 ≤ Couter) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x M T R S : ℝ),
      4 ≤ x → 1 ≤ M → 1 ≤ T → x = 4*M*T →
      1 ≤ R → 1 ≤ S → R*S ≤ x →
      ∀ (N : Finset ℕ) (a : ℤ) (b : ℕ) (K : WExtractedKey)
        (F : ℕ) (j : Fin 5 → ℕ) (positive : Bool) (t : WExtractedTuple × ℤ),
      (∀ n ∈ N, 0 < n) → (∀ n ∈ N, (n : ℝ) ≤ 2*T) →
      (F : ℝ) ≤ 2*T → K ∈ wExtractedKeyBox (x^η) →
      t ∈ wAnalyticDyadicBlock
        (wExtractedKeyFiber (wFloorCutoff M (x^η)) N (Ioc 0 ⌊R*S⌋₊) a
          (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive →
      wBlockAmplitude K j * Real.sqrt (directJoinedMass ρ Couter x T j) *
        Real.sqrt (directJoinedZero ε ρ Czero Ccoeff x K F j) / T^2 ≤
      C * x^(100*(ε+ρ+η)) * (R*Real.sqrt S/Real.sqrt x) := by
  let B := Ccoeff^4*Couter*Czero
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨32*(B+1), by positivity, ?_⟩
  intro x M T R S hx hM hT hMT hR hS hRS N a b K F j positive t hN hNT hF hK ht
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hM0 : 0 < M := by linarith
  have hT0 : 0 < T := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hTx : T ≤ x := by nlinarith
  have hRx : R ≤ x := (le_mul_of_one_le_right hR0 hS).trans hRS
  have hSx : S ≤ x := (le_mul_of_one_le_left hS0 hR).trans hRS
  have hZ : 0 ≤ x^η := Real.rpow_nonneg hx0.le η
  have hZx : x^η ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hη1
  have hQ : ∀ q ∈ Ioc 0 ⌊R*S⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hD := (wExtractedKeyFiber_positive hN hQ (mem_filter.mp ht).1).1
  obtain ⟨hk, hr, hs⟩ := directLocalScale_fullLevel_coordinates hN
    (mul_nonneg hR0 hS0) hR0 hS0 ht
  have hn := directPayZero_n_le hN hQ ht hNT
  have hfreq := directLocalScale_floor_frequency_le hM0 hZ hN hQ ht
  rw [directLocalScale_frequency_change_variables hM0.ne' hT0.ne' hMT] at hfreq
  have hDx : (K.D : ℝ) ≤ x^3 :=
    (directLocalScale_key_bounds hZ hK).1.trans (by gcongr)
  have hd : (K.1.2.1 : ℝ) ≤ x := by
    have hh := (mem_wExtractedKeyBox_iff.mp hK).2.1
    exact ((Nat.cast_le.mpr hh).trans (Nat.floor_le hZ)).trans hZx
  have hHx : (2 : ℝ)^j 0 ≤ x^10 := by
    calc
      _ ≤ 32*((K.D : ℝ)*2^j 1*2^j 3*2^j 4)*(x^η)*T/x := hfreq
      _ ≤ 32*(x^3*x*x*x)*x*x/x := by
        gcongr
        · exact hk.trans hRS
        · exact hr.trans hRx
        · exact hs.trans hSx
      _ = 32*x^7 := by field_simp
      _ ≤ x^3*x^7 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg (x-4)]
      _ = _ := by ring
  have he := directPayZero_envelope hx hT0.le hTx hε K F j hF hn
    (hs.trans hSx) hd hHx
  have hh := directPayZero_square (ε := ε) (ρ := ρ) hCz hCc hCo hx0 hT0 hZ hR0 hS0 K F j hD
    hF hn hk hr hfreq
  have hpow : x^(5*ρ) * x^(44*ε) * x^η ≤ (x^(100*(ε+ρ+η)))^2 := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0,
      ← Real.rpow_natCast (x^(100*(ε+ρ+η))) 2, ← Real.rpow_mul hx0.le]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    norm_num
    linarith
  have hconst : 1024*B ≤ (32*(B+1))^2 := by nlinarith [sq_nonneg B]
  have hbase : (R*Real.sqrt S/Real.sqrt x)^2 = R^2*S/x := by
    rw [div_pow, mul_pow, Real.sq_sqrt hS0, Real.sq_sqrt hx0.le]
  have hfinal : (wBlockAmplitude K j * Real.sqrt (directJoinedMass ρ Couter x T j) *
      Real.sqrt (directJoinedZero ε ρ Czero Ccoeff x K F j) / T^2)^2 ≤
      (32*(B+1)*x^(100*(ε+ρ+η))*(R*Real.sqrt S/Real.sqrt x))^2 := by
    calc
      _ ≤ 1024*B*x^(5*ρ)*x^(44*ε)*x^η*(R^2*S/x) := by
        apply hh.trans
        dsimp [B]
        gcongr
      _ = (1024*B)*(x^(5*ρ)*x^(44*ε)*x^η)*(R^2*S/x) := by ring
      _ ≤ (32*(B+1))^2*(x^(100*(ε+ρ+η)))^2*(R^2*S/x) := by
        gcongr
      _ = _ := by rw [mul_pow, mul_pow, hbase]; ring
  exact (sq_le_sq₀ (by unfold wBlockAmplitude; positivity) (by positivity)).mp hfinal

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

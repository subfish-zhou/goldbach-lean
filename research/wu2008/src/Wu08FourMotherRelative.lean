import Wu08FourMotherIdentity

noncomputable section
open Real MeasureTheory Wu2008DoubleSieve Filter
open scoped Topology
namespace Wu08FourMother
open MathlibNt.SieveTheory.SingularSeries
open Wu08FirstPrimeFour.SmallBoundaryRecovery

/-- The original normalization is preserved literally, not replaced by N/log²N. -/
theorem scale_lower {N : ℕ} (hN : 0 < N) :
    liuUniversalProduct*((N : ℝ)/log N^2) ≤ U8CanonicalMother.M N := by
  rw [U8CanonicalMother.scale_eq_liu hN]
  calc
    _ ≤ liuSingularSeries N*((N : ℝ)/log N^2) :=
      mul_le_mul_of_nonneg_right (liuUniversalProduct_le_liuSingularSeries N) (by positivity)
    _ = _ := by ring

/-- An actual relative payment of the raw N/log^A term; A=3 is fixed before N.
The positive universal singular-series factor is retained in the log threshold. -/
theorem raw_error_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      (N : ℝ)/log N^3 ≤ ε*U8CanonicalMother.M N := by
  have hc : 0 < ε*liuUniversalProduct := mul_pos hε liuUniversalProduct_pos
  have ht : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (1/(ε*liuUniversalProduct))))
  refine ⟨max T 4,le_max_right _ _,fun N hN => ?_⟩
  have hN4 : 4 ≤ N := (le_max_right T 4).trans hN
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hb := hT N ((le_max_left T 4).trans hN)
  have hinv : 1/log N ≤ ε*liuUniversalProduct := by
    apply (div_le_iff₀ hlog).mpr
    have := (div_le_iff₀ hc).mp hb
    nlinarith only [this]
  calc
    _ = (1/log N)*((N : ℝ)/log N^2) := by ring
    _ ≤ (ε*liuUniversalProduct)*((N : ℝ)/log N^2) :=
      mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = ε*(liuUniversalProduct*((N : ℝ)/log N^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (scale_lower (by omega)) hε.le

/-- Relative count upper from the new actual original-pair producer, not from
monotonicity of two integrals. The raw remainder is paid once at its real scale. -/
theorem original_pair_paid {σ : ℝ} (hσ : 0 < σ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
        (originalIntegral false+originalIntegral true+σ)*U8CanonicalMother.M N := by
  obtain ⟨Tq,_,hq⟩ := original_pair_integral_upper (half_pos hσ) 3
  obtain ⟨Tr,hr,hraw⟩ := raw_error_paid (half_pos hσ)
  obtain ⟨Tn,hTn⟩ := exists_nat_ge Tq
  refine ⟨max Tn Tr,by omega,fun N hN he => ?_⟩
  have hqN := hq N (hTn.trans (by exact_mod_cast (show Tn ≤ N by omega))) he
  have hrN := hraw N (by omega)
  change _ ≤ _*U8CanonicalMother.M N+_ at hqN
  linarith only [hqN,hrN]

end Wu08FourMother

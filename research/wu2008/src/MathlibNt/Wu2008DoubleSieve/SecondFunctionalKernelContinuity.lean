import MathlibNt.Wu2008DoubleSieve.SecondFunctionalKernelContinuityFamilies
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalKernelContinuityUnit

/-! Continuity of the literal fourteen-term same-phi kernel, for arbitrary
mother parameters. No continuity assumption is supplied by the caller. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set
open scoped BigOperators

/-- The original common-parameter kernel is continuous, even before restriction. -/
theorem kernel_continuous (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : Continuous (SecondFunctionalCoupled.kernel p) := by
  have hl (j : Fin 6) := lower_K_continuous
    (LowerTripleContinuous.mother_compact_parameters p hp hs) j
  have hf (j : Fin 4) := four_legalK_continuous
    (FourPrimeNonunit.legalK_mother_compact p hp hs) j
  obtain ⟨ha, haa, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  exact (continuous_finsetSum _ (fun j _ => hl j)).add
    ((((unit_J20_continuous ha hb).add (unit_J21_continuous (ha.trans haa) hb)).add
      ((high_K20_continuous ha hb).add (high_K21_continuous (ha.trans haa) hb))).add
      (continuous_finsetSum _ (fun j _ => hf j)))

/-- The advertised closed half-line includes the endpoint phi = 2. -/
theorem kernel_continuousOn_Ici (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : ContinuousOn (SecondFunctionalCoupled.kernel p) (Ici 2) :=
  (kernel_continuous p hp hs).continuousOn

end Wu2008DoubleSieve.SecondFunctionalJointTail

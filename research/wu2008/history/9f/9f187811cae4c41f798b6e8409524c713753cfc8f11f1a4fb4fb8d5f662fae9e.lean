import SrcSixthGainConsumer
import SrcSixthGainOriginal

noncomputable section
namespace WuSource.SrcSixthGain
open Real Wu2008DoubleSieve NodeExtension ActualNineFeedback
open scoped Classical BigOperators

def frozenGain : ℝ := conservative (transferred Wu04Bypass.v8)

theorem frozen_sixth_lower : SixthSlotAssembly.SixthLower frozenGain := by
  obtain ⟨d0,hd0,_,hx⟩ := Wu04Bypass.new_nine_actual
  exact sixth_lower Wu04Bypass.v8_nonneg
    (matrixApply_nonneg transferMatrix_nonneg Wu04Bypass.v8_nonneg)
    (fun _ => le_rfl) hd0 hx

theorem frozen_actual_sixth {eps : ℝ} (heps : 0 < eps) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((381/100 : ℝ)+frozenGain-eps)*U8CanonicalMother.M N ≤ SixthSlotCore.sixth N := by
  obtain ⟨d0,hd0,_,hx⟩ := Wu04Bypass.new_nine_actual
  exact actual_sixth_classical_lower Wu04Bypass.v8_nonneg
    (matrixApply_nonneg transferMatrix_nonneg Wu04Bypass.v8_nonneg)
    (fun _ => le_rfl) hd0 hx heps

theorem frozen_whole_source :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1/10 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ d0 →
        8*(∑ j : Fin 21, g6Weight j*transferred Wu04Bypass.v8 j) ≤
          paperG6 (wuImprovementLimit false delta) := by
  obtain ⟨d0,hd0,hcap,hx⟩ := Wu04Bypass.new_nine_actual
  refine ⟨d0,hd0,hcap,?_⟩
  intro delta hd hdd0
  have hdhi : delta ≤ 1/10 := by linarith [hdd0.trans hcap]
  exact original_whole_source_lower hd hdhi (WuTarget.W01.transferred_actual hd hdhi (hx delta hd hdd0))

theorem frozen_ordinary_count {eps dmax : ℝ} (heps : 0 < eps) (hdmax : 0 < dmax) :
    ∃ delta : ℝ, 0 < delta ∧ delta < dmax ∧ delta ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (sourceCoefficient frozenGain-eps)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨d0,hd0,_,hx⟩ := Wu04Bypass.new_nine_actual
  obtain ⟨delta,hd,hdmax',_,hdhi,T,hT,hc⟩ := ordinary_count Wu04Bypass.v8_nonneg
    (matrixApply_nonneg transferMatrix_nonneg Wu04Bypass.v8_nonneg)
    (fun _ => le_rfl) hd0 hx heps hdmax
  exact ⟨delta,hd,hdmax',hdhi,T,hT,hc⟩

#check @original_whole_source_lower
#check @published_twentyone
#check @first_fourteen
#check @fifteenth_crossing
#check @middle_five
#check @last_truncated
#check @full_weights_same_profile_debit
#check @full_weights_capped
#check @unaffected_weight
#check @no_prop43_ceiling_on_first
#check @no_prop43_ceiling_on_second
#check @source_high_multiple_annihilation
#check @conservative_le_net
#check @sixth_lower
#check @actual_sixth_classical_lower
#check @ordinary_count
#check @frozen_actual_sixth
#check @frozen_whole_source
#check @frozen_ordinary_count
#print axioms original_whole_source_lower
#print axioms published_twentyone
#print axioms fifteenth_crossing
#print axioms last_truncated
#print axioms no_prop43_ceiling_on_first
#print axioms no_prop43_ceiling_on_second
#print axioms source_high_multiple_annihilation
#print axioms full_weights_same_profile_debit
#print axioms full_weights_capped
#print axioms unaffected_weight
#print axioms frozen_sixth_lower
#print axioms frozen_actual_sixth
#print axioms frozen_whole_source
#print axioms frozen_ordinary_count

end WuSource.SrcSixthGain

open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "WuSource.SrcSixthGain." &&
        (name.toString.splitOn "._").length == 1 then
      logInfo m!"DECLARATION {name} : {info.type}"

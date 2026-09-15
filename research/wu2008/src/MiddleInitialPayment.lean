import MiddleInitialFTC

noncomputable section
open Real Wu2008DoubleSieve
open SharpLogRecurrence JointLogTotalComparison
namespace MiddleInitialPayment
open MiddleInitialFTC

/-- Collection of the whole old-minus-new signed integral, before log payment. -/
def paid (L H : ℝ → ℝ) : ℝ :=
  54184986258433847/7671098066888025+
  (299524880/916839)*L (5/4)-
  (8547286566790892748321251/2986096125885620562045000)*H (527/327)-
  (1151264258336/12882918447)*H (4/3)-
  (1766372040448/5150827583)*H (7/6)

theorem collected : gainReal = paid log log := by
  have h54 := log_div (by norm_num : (5:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0)
  have h43 := log_div (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)
  have h76 := log_div (by norm_num : (7:ℝ) ≠ 0) (by norm_num : (6:ℝ) ≠ 0)
  have hh := log_div (by norm_num : (527/200:ℝ) ≠ 0) (by norm_num : (327/200:ℝ) ≠ 0)
  norm_num at hh
  norm_num [gainReal,primitive,polePrimitive,paid,h]
  linarith only [h54,h43,h76,hh]

theorem payment : paid lowerLog V ≤ gainReal ∧ gainReal ≤ paid V lowerLog := by
  rw [collected]
  have l0 := log_lower (by norm_num : (1:ℝ) ≤ 5/4)
  have u0 := log_le_V (by norm_num : (1:ℝ) ≤ 5/4)
  have l1 := log_lower (by norm_num : (1:ℝ) ≤ 527/327)
  have u1 := log_le_V (by norm_num : (1:ℝ) ≤ 527/327)
  have l2 := log_lower (by norm_num : (1:ℝ) ≤ 4/3)
  have u2 := log_le_V (by norm_num : (1:ℝ) ≤ 4/3)
  have l3 := log_lower (by norm_num : (1:ℝ) ≤ 7/6)
  have u3 := log_le_V (by norm_num : (1:ℝ) ≤ 7/6)
  unfold paid
  constructor <;> linarith only [l0,u0,l1,u1,l2,u2,l3,u3]

def gain : ℝ := paid lowerLog V

theorem gain_exact : gain = 283206217936523016471739025698/12052282150995822203076178655085 := by
  norm_num [gain,paid,lowerLog,upperLog,V]

theorem gain_bounds : (23498/1000000:ℝ) < gain ∧ gain < 23499/1000000 := by
  rw [gain_exact]
  norm_num

theorem true_gain_bounds : (23498/1000000:ℝ) < gainReal ∧ gainReal < 29135/1000000 := by
  have hu : paid V lowerLog < (29135/1000000:ℝ) := by norm_num [paid,V,lowerLog,upperLog]
  exact ⟨gain_bounds.1.trans_le payment.1,payment.2.trans_lt hu⟩

/-- Only this middle upper is replaced. No lower-side recovery is reused. -/
def newMiddleUpper : ℝ := ExactWeightTripleEnclosure.middleUpper-gain

theorem middle_upper : BaseGSharedActualRecovery.middleKernel ≤ newMiddleUpper := by
  have hm := MiddleInitialFTC.middle_upper
  have hp := payment.1
  unfold newMiddleUpper gain
  linarith only [hm,hp]

theorem middle_descent : (23498/1000000:ℝ) < ExactWeightTripleEnclosure.middleUpper-newMiddleUpper := by
  unfold newMiddleUpper
  linarith only [gain_bounds.1]

end MiddleInitialPayment

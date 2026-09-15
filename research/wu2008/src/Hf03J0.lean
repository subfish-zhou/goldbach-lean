import RemainingHfParentDiagonal
namespace Hf03Scalar
open Real RemainingHf Wu2008DoubleSieve NodeExtension ActualNineFeedback FirstFeedbackIntegrals
open FirstErrorFullPayment Wu04FactorEnvelopes SharpLogRecurrence JointLogTotalComparison F1FullRecoveryPayment
open FiniteEndpointPayment CoupledJLogRecovery CoupledIntegralRecovery
noncomputable section
theorem j0_active : RemainingHf.jPaid (firstS (0 : Fin 5)) (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5)))
    (left (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (0 : Fin 9))
    (right (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (0 : Fin 9)) = (436441897392211518664424522531847612074912189603707497820927404296604496810132204645887760773649500074690993177552088815395476752826552482623268867850486722170125129809900103392590323045910062470400262940106520682724233260583351/7224307715892658937484748796492107145369400700679249459035471246052263978258521742807572395784355716895359727808034781775373368346818493434841878242222846195295473330637326908991883664407832339017392985631969973236034131580571250 : ℝ) := by
  norm_num [RemainingHf.jPaid,signed,splitLower,splitUpper,basicLower,basicUpper,lowerGapPayment,upperGapPayment,F1LowerResidual.payment,F1LowerResidual.denom,leftFactor,rightFactor,lowerLog,upperLog,V,firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,
    qa,qb,qc,qd,qe,pa,pb,pc,pd,ra,rb,rc,rd,re]

theorem j0_empty_1 : RemainingHf.jPaid (firstS (0 : Fin 5)) (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5)))
    (left (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (1 : Fin 9))
    (right (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (1 : Fin 9)) = 0 := by
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j0_empty_2 : RemainingHf.jPaid (firstS (0 : Fin 5)) (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5)))
    (left (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (2 : Fin 9))
    (right (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (2 : Fin 9)) = 0 := by
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j0_empty_3 : RemainingHf.jPaid (firstS (0 : Fin 5)) (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5)))
    (left (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (3 : Fin 9))
    (right (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (3 : Fin 9)) = 0 := by
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j0_empty_4 : RemainingHf.jPaid (firstS (0 : Fin 5)) (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5)))
    (left (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (4 : Fin 9))
    (right (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (4 : Fin 9)) = 0 := by
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j0_empty_5 : RemainingHf.jPaid (firstS (0 : Fin 5)) (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5)))
    (left (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (5 : Fin 9))
    (right (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (5 : Fin 9)) = 0 := by
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j0_empty_6 : RemainingHf.jPaid (firstS (0 : Fin 5)) (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5)))
    (left (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (6 : Fin 9))
    (right (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (6 : Fin 9)) = 0 := by
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j0_empty_7 : RemainingHf.jPaid (firstS (0 : Fin 5)) (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5)))
    (left (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (7 : Fin 9))
    (right (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (7 : Fin 9)) = 0 := by
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j0_empty_8 : RemainingHf.jPaid (firstS (0 : Fin 5)) (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5)))
    (left (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (8 : Fin 9))
    (right (jStart (firstNode (0 : Fin 5)) (firstS (0 : Fin 5))-1) ((firstS (0 : Fin 5))-2) (8 : Fin 9)) = 0 := by
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

end
end Hf03Scalar

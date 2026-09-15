import RemainingHfParentDiagonal
namespace Hf03Scalar
open Real RemainingHf Wu2008DoubleSieve NodeExtension ActualNineFeedback FirstFeedbackIntegrals
open FirstErrorFullPayment Wu04FactorEnvelopes SharpLogRecurrence JointLogTotalComparison F1FullRecoveryPayment
open FiniteEndpointPayment CoupledJLogRecovery CoupledIntegralRecovery
noncomputable section
theorem j3_active : RemainingHf.jPaid (firstS (3 : Fin 5)) (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5)))
    (left (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (0 : Fin 9))
    (right (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (0 : Fin 9)) = (22743883031466661371788891738030174859353943303166439055379733660645966004986833269328554684641121868374619257867843121550555532808025088143/3733067649747369994688908942336436137106348384384089450753160015046196757787669460814664558688602716824095050799799588558912145935405831380000 : ℝ) := by
  dsimp only [firstS,Matrix.cons_val_three]
  norm_num [RemainingHf.jPaid,signed,splitLower,splitUpper,basicLower,basicUpper,lowerGapPayment,upperGapPayment,F1LowerResidual.payment,F1LowerResidual.denom,leftFactor,rightFactor,lowerLog,upperLog,V,firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,
    qa,qb,qc,qd,qe,pa,pb,pc,pd,ra,rb,rc,rd,re]

theorem j3_empty_1 : RemainingHf.jPaid (firstS (3 : Fin 5)) (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5)))
    (left (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (1 : Fin 9))
    (right (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (1 : Fin 9)) = 0 := by
  dsimp only [firstS,Matrix.cons_val_three]
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j3_empty_2 : RemainingHf.jPaid (firstS (3 : Fin 5)) (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5)))
    (left (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (2 : Fin 9))
    (right (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (2 : Fin 9)) = 0 := by
  dsimp only [firstS,Matrix.cons_val_three]
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j3_empty_3 : RemainingHf.jPaid (firstS (3 : Fin 5)) (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5)))
    (left (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (3 : Fin 9))
    (right (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (3 : Fin 9)) = 0 := by
  dsimp only [firstS,Matrix.cons_val_three]
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j3_empty_4 : RemainingHf.jPaid (firstS (3 : Fin 5)) (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5)))
    (left (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (4 : Fin 9))
    (right (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (4 : Fin 9)) = 0 := by
  dsimp only [firstS,Matrix.cons_val_three]
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j3_empty_5 : RemainingHf.jPaid (firstS (3 : Fin 5)) (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5)))
    (left (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (5 : Fin 9))
    (right (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (5 : Fin 9)) = 0 := by
  dsimp only [firstS,Matrix.cons_val_three]
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j3_empty_6 : RemainingHf.jPaid (firstS (3 : Fin 5)) (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5)))
    (left (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (6 : Fin 9))
    (right (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (6 : Fin 9)) = 0 := by
  dsimp only [firstS,Matrix.cons_val_three]
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j3_empty_7 : RemainingHf.jPaid (firstS (3 : Fin 5)) (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5)))
    (left (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (7 : Fin 9))
    (right (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (7 : Fin 9)) = 0 := by
  dsimp only [firstS,Matrix.cons_val_three]
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

theorem j3_empty_8 : RemainingHf.jPaid (firstS (3 : Fin 5)) (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5)))
    (left (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (8 : Fin 9))
    (right (jStart (firstNode (3 : Fin 5)) (firstS (3 : Fin 5))-1) ((firstS (3 : Fin 5))-2) (8 : Fin 9)) = 0 := by
  dsimp only [firstS,Matrix.cons_val_three]
  norm_num [firstS,firstNode,jStart,left,right,clip,upperLeft,upperNode,Fin.val_natCast]
  apply RemainingHfParent.jPaid_diagonal <;> norm_num

end
end Hf03Scalar

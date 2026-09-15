import MathlibNt.SieveTheory.LiLiuPrereqBuchstabPrimeSums
import AnalyticNumberTheory.Mertens.PartialSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open AnalyticNumberTheory.Mertens (primeReciprocalSum primesUpTo mem_primesUpTo
  primesUpTo_mono mertensSecond_eventually mertensSecondConstant)
#check primesIoc
#print LiLiuPrereqBuchstab.primesIoc
#print LiLiuPrereqBuchstab.mem_primesIoc
#check Nat.le_floor_iff
#check Finset.sum_sdiff
#check integral_inv_div_log
#check integral_one_div_of_pos
#check mertensSecond_eventually
#print axioms AnalyticNumberTheory.Mertens.mertensSecond_eventually

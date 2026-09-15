import Wu18938Campaign.M3.Confirmed.TableRow00
import Wu18938Campaign.M3.Confirmed.TableRow01
import Wu18938Campaign.M3.Confirmed.TableRow02
import Wu18938Campaign.M3.Confirmed.TableRow03
import Wu18938Campaign.M3.Confirmed.TableRow04
import Wu18938Campaign.M3.Confirmed.TableRow05
import Wu18938Campaign.M3.Confirmed.TableRow06
import Wu18938Campaign.M3.Confirmed.TableRow07
import Wu18938Campaign.M3.Confirmed.TableRow08
import Wu18938Campaign.M3.Confirmed.TableRow09
import Wu18938Campaign.M3.Confirmed.TableRow10
import Wu18938Campaign.M3.Confirmed.TableRow11
import Wu18938Campaign.M3.Confirmed.TableRow12
import Wu18938Campaign.M3.Confirmed.TableRow13
import Wu18938Campaign.M3.Confirmed.TableRow14
import Wu18938Campaign.M3.Confirmed.TableRow15
import Wu18938Campaign.M3.Confirmed.TableRow16
import Wu18938Campaign.M3.Confirmed.TableRow17
import Wu18938Campaign.M3.Confirmed.TableRow18
import Wu18938Campaign.M3.Confirmed.TableRow19
import Wu18938Campaign.M3.Confirmed.TableRow20
import Wu18938Campaign.M3.Confirmed.TableRow21

noncomputable section
namespace Wu18938Campaign.M3.Confirmed
open Real Set MeasureTheory QuarterTrim NodeExtension
open WuSource.SrcSixthGain ActualNineFeedback

def literalTableGain : ℝ := 8 * ∑ j : Fin 21, g6Weight j * originalHeight j

theorem literalTableGain_published :
    literalTableGain = Wu08G6High.published originalHeight :=
  (published_twentyone originalHeight).symm

theorem literalTableGain_certificate :
    (1114814024867291971 / 18446744073709551616 : ℝ) ≤ literalTableGain := by
  have hi (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ endpoint) :
      IntervalIntegrable density volume a b := by
    apply density_integrable.mono_set
    rw [uIcc_of_le scalar_interval, uIcc_of_le hab]
    exact Icc_subset_Icc ha hb
  have hs : (34 / 10 : ℝ) ≤ split := breakpoints.2.2.1.le
  have ht : split ≤ (35 / 10 : ℝ) := breakpoints.2.2.2.1.le
  have hcross := intervalIntegral.integral_add_adjacent_intervals
    (hi (34 / 10) split (by norm_num) hs (by norm_num [split, endpoint, alpha, beta]))
    (hi split (35 / 10) (by norm_num [split, alpha, beta]) ht
      (by norm_num [endpoint, alpha, beta]))
  norm_num [split, alpha, beta] at hcross
  unfold literalTableGain
  norm_num [Fin.sum_univ_succ, originalHeight, originalRow, Wu08Staircase.table,
    g6Weight, cellEnd, rNode, endpoint, alpha, beta]
  linarith only [TableRow00.lower, TableRow01.lower, TableRow02.lower, TableRow03.lower, TableRow04.lower, TableRow05.lower, TableRow06.lower, TableRow07.lower, TableRow08.lower, TableRow09.lower, TableRow10.lower, TableRow11.lower, TableRow12.lower, TableRow13.lower, TableRow14.lower, TableRow15.lower, TableRow16.lower, TableRow17.lower, TableRow18.lower, TableRow19.lower, TableRow20.lower, TableRow21.lower, hcross]

theorem literalTableGain_gt_six_percent : (3 / 50 : ℝ) < literalTableGain := by
  have h := literalTableGain_certificate
  linarith only [h]

end Wu18938Campaign.M3.Confirmed

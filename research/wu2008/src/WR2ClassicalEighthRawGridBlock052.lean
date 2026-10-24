import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints052
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_052 (j : Fin 16) : upperValue ((point (16*52+j.val)+point ((16*52+j.val)+1))/2) ≤ payment (16*52+j.val) := by
  fin_cases j
  · change upperValue ((point (832)+point ((832)+1))/2) ≤ payment (832)
    have hp : payment 832 = (2558343613674:ℝ)/1000000000000 := rfl
    have hx : (point 832+point 833)/2 = (979585:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_832
  · change upperValue ((point (833)+point ((833)+1))/2) ≤ payment (833)
    have hp : payment 833 = (2555197660087:ℝ)/1000000000000 := rfl
    have hx : (point 833+point 834)/2 = (2940809:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_833
  · change upperValue ((point (834)+point ((834)+1))/2) ≤ payment (834)
    have hp : payment 834 = (2552055226889:ℝ)/1000000000000 := rfl
    have hx : (point 834+point 835)/2 = (2942863:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_834
  · change upperValue ((point (835)+point ((835)+1))/2) ≤ payment (835)
    have hp : payment 835 = (2548916306080:ℝ)/1000000000000 := rfl
    have hx : (point 835+point 836)/2 = (981639:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_835
  · change upperValue ((point (836)+point ((836)+1))/2) ≤ payment (836)
    have hp : payment 836 = (2545780889678:ℝ)/1000000000000 := rfl
    have hx : (point 836+point 837)/2 = (2946971:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_836
  · change upperValue ((point (837)+point ((837)+1))/2) ≤ payment (837)
    have hp : payment 837 = (2542648969723:ℝ)/1000000000000 := rfl
    have hx : (point 837+point 838)/2 = (2949025:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_837
  · change upperValue ((point (838)+point ((838)+1))/2) ≤ payment (838)
    have hp : payment 838 = (2539520538279:ℝ)/1000000000000 := rfl
    have hx : (point 838+point 839)/2 = (983693:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_838
  · change upperValue ((point (839)+point ((839)+1))/2) ≤ payment (839)
    have hp : payment 839 = (2536395587430:ℝ)/1000000000000 := rfl
    have hx : (point 839+point 840)/2 = (2953133:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_839
  · change upperValue ((point (840)+point ((840)+1))/2) ≤ payment (840)
    have hp : payment 840 = (2533274109280:ℝ)/1000000000000 := rfl
    have hx : (point 840+point 841)/2 = (2955187:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_840
  · change upperValue ((point (841)+point ((841)+1))/2) ≤ payment (841)
    have hp : payment 841 = (2530156095956:ℝ)/1000000000000 := rfl
    have hx : (point 841+point 842)/2 = (985747:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_841
  · change upperValue ((point (842)+point ((842)+1))/2) ≤ payment (842)
    have hp : payment 842 = (2527041539607:ℝ)/1000000000000 := rfl
    have hx : (point 842+point 843)/2 = (2959295:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_842
  · change upperValue ((point (843)+point ((843)+1))/2) ≤ payment (843)
    have hp : payment 843 = (2523930432402:ℝ)/1000000000000 := rfl
    have hx : (point 843+point 844)/2 = (2961349:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_843
  · change upperValue ((point (844)+point ((844)+1))/2) ≤ payment (844)
    have hp : payment 844 = (2520822766531:ℝ)/1000000000000 := rfl
    have hx : (point 844+point 845)/2 = (987801:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_844
  · change upperValue ((point (845)+point ((845)+1))/2) ≤ payment (845)
    have hp : payment 845 = (2517718534205:ℝ)/1000000000000 := rfl
    have hx : (point 845+point 846)/2 = (2965457:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_845
  · change upperValue ((point (846)+point ((846)+1))/2) ≤ payment (846)
    have hp : payment 846 = (2514617727658:ℝ)/1000000000000 := rfl
    have hx : (point 846+point 847)/2 = (2967511:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_846
  · change upperValue ((point (847)+point ((847)+1))/2) ≤ payment (847)
    have hp : payment 847 = (2511520339141:ℝ)/1000000000000 := rfl
    have hx : (point 847+point 848)/2 = (989855:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_847
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_052

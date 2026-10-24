import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints135
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_135 (j : Fin 16) : lowerPayment (16*135+j.val) ≤
    lowerValue ((point 2 split 4096 (16*135+j.val)+point 2 split 4096 (16*135+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2160 ≤ lowerValue ((point 2 split 4096 2160+point 2 split 4096 2161)/2)
    have hp : lowerPayment 2160 = (247165825025:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2160+point 2 split 4096 2161)/2 = (463385451:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463385451:ℝ)/168755200)/ClassicalSixthBranch.v ((463385451:ℝ)/168755200) = (646978984027:ℝ)/316857417624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2160
  · change lowerPayment 2161 ≤ lowerValue ((point 2 split 4096 2161+point 2 split 4096 2162)/2)
    have hp : lowerPayment 2161 = (247255476478:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2161+point 2 split 4096 2162)/2 = (463443713:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463443713:ℝ)/168755200)/ClassicalSixthBranch.v ((463443713:ℝ)/168755200) = (646901670353:ℝ)/316809409736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2161
  · change lowerPayment 2162 ≤ lowerValue ((point 2 split 4096 2162+point 2 split 4096 2163)/2)
    have hp : lowerPayment 2162 = (247345120365:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2162+point 2 split 4096 2163)/2 = (18540079:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18540079:ℝ)/6750208)/ClassicalSixthBranch.v ((18540079:ℝ)/6750208) = (646824356679:ℝ)/316761401848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2162
  · change lowerPayment 2163 ≤ lowerValue ((point 2 split 4096 2163+point 2 split 4096 2164)/2)
    have hp : lowerPayment 2163 = (247434756700:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2163+point 2 split 4096 2164)/2 = (463560237:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463560237:ℝ)/168755200)/ClassicalSixthBranch.v ((463560237:ℝ)/168755200) = (129349408601:ℝ)/63342678792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2163
  · change lowerPayment 2164 ≤ lowerValue ((point 2 split 4096 2164+point 2 split 4096 2165)/2)
    have hp : lowerPayment 2164 = (247524385500:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2164+point 2 split 4096 2165)/2 = (463618499:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463618499:ℝ)/168755200)/ClassicalSixthBranch.v ((463618499:ℝ)/168755200) = (646669729331:ℝ)/316665386072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2164
  · change lowerPayment 2165 ≤ lowerValue ((point 2 split 4096 2165+point 2 split 4096 2166)/2)
    have hp : lowerPayment 2165 = (247614006780:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2165+point 2 split 4096 2166)/2 = (463676761:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463676761:ℝ)/168755200)/ClassicalSixthBranch.v ((463676761:ℝ)/168755200) = (646592415657:ℝ)/316617378184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2165
  · change lowerPayment 2166 ≤ lowerValue ((point 2 split 4096 2166+point 2 split 4096 2167)/2)
    have hp : lowerPayment 2166 = (247703620556:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2166+point 2 split 4096 2167)/2 = (463735023:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463735023:ℝ)/168755200)/ClassicalSixthBranch.v ((463735023:ℝ)/168755200) = (646515101983:ℝ)/316569370296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2166
  · change lowerPayment 2167 ≤ lowerValue ((point 2 split 4096 2167+point 2 split 4096 2168)/2)
    have hp : lowerPayment 2167 = (247793226844:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2167+point 2 split 4096 2168)/2 = (92758657:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92758657:ℝ)/33751040)/ClassicalSixthBranch.v ((92758657:ℝ)/33751040) = (646437788309:ℝ)/316521362408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2167
  · change lowerPayment 2168 ≤ lowerValue ((point 2 split 4096 2168+point 2 split 4096 2169)/2)
    have hp : lowerPayment 2168 = (247882825660:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2168+point 2 split 4096 2169)/2 = (463851547:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463851547:ℝ)/168755200)/ClassicalSixthBranch.v ((463851547:ℝ)/168755200) = (129272094927:ℝ)/63294670904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2168
  · change lowerPayment 2169 ≤ lowerValue ((point 2 split 4096 2169+point 2 split 4096 2170)/2)
    have hp : lowerPayment 2169 = (247972417019:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2169+point 2 split 4096 2170)/2 = (463909809:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463909809:ℝ)/168755200)/ClassicalSixthBranch.v ((463909809:ℝ)/168755200) = (646283160961:ℝ)/316425346632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2169
  · change lowerPayment 2170 ≤ lowerValue ((point 2 split 4096 2170+point 2 split 4096 2171)/2)
    have hp : lowerPayment 2170 = (248062000937:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2170+point 2 split 4096 2171)/2 = (463968071:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463968071:ℝ)/168755200)/ClassicalSixthBranch.v ((463968071:ℝ)/168755200) = (646205847287:ℝ)/316377338744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2170
  · change lowerPayment 2171 ≤ lowerValue ((point 2 split 4096 2171+point 2 split 4096 2172)/2)
    have hp : lowerPayment 2171 = (248151577430:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2171+point 2 split 4096 2172)/2 = (464026333:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464026333:ℝ)/168755200)/ClassicalSixthBranch.v ((464026333:ℝ)/168755200) = (646128533613:ℝ)/316329330856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2171
  · change lowerPayment 2172 ≤ lowerValue ((point 2 split 4096 2172+point 2 split 4096 2173)/2)
    have hp : lowerPayment 2172 = (248241146513:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2172+point 2 split 4096 2173)/2 = (92816919:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92816919:ℝ)/33751040)/ClassicalSixthBranch.v ((92816919:ℝ)/33751040) = (646051219939:ℝ)/316281322968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2172
  · change lowerPayment 2173 ≤ lowerValue ((point 2 split 4096 2173+point 2 split 4096 2174)/2)
    have hp : lowerPayment 2173 = (248330708204:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2173+point 2 split 4096 2174)/2 = (464142857:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464142857:ℝ)/168755200)/ClassicalSixthBranch.v ((464142857:ℝ)/168755200) = (129194781253:ℝ)/63246663016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2173
  · change lowerPayment 2174 ≤ lowerValue ((point 2 split 4096 2174+point 2 split 4096 2175)/2)
    have hp : lowerPayment 2174 = (248420262516:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2174+point 2 split 4096 2175)/2 = (464201119:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464201119:ℝ)/168755200)/ClassicalSixthBranch.v ((464201119:ℝ)/168755200) = (645896592591:ℝ)/316185307192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2174
  · change lowerPayment 2175 ≤ lowerValue ((point 2 split 4096 2175+point 2 split 4096 2176)/2)
    have hp : lowerPayment 2175 = (248509809466:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2175+point 2 split 4096 2176)/2 = (464259381:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((464259381:ℝ)/168755200)/ClassicalSixthBranch.v ((464259381:ℝ)/168755200) = (645819278917:ℝ)/316137299304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2175
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_135

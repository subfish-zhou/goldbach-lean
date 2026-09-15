import FreshLogBasis

noncomputable section
open Real FirstCRationalPayment F1JointFTC F1ActualSecondFTC F1BFullFTC FreshLogBasis
namespace FreshLogEndpoints

namespace AOne
open F1FreshFTC.AOne
def rational : ℝ := poleR (0) c0_2 c0_3 c0_4+
  poleR (-2) c1_2 c1_3 c1_4+
  poleR (-1327/200) c2_2 c2_3 c2_4+p0*(927/200-2)+(p1/2)*((927/200)^2-2^2)

def collected : ℝ := c0_1*log (927/400)+
  c1_1*log (refOne)+
  c2_1*log (2254/1727)+
  (f)*log refOne+aMinus f g*log crossOneMinus-aPlus f g*log crossOnePlus+rational

theorem collected_exact : mass = collected := by
  have h0 := pole_difference (0) c0_1 c0_2 c0_3 c0_4 (927/400)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h1 := pole_difference (-2) c1_1 c1_2 c1_3 c1_4 (refOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h2 := pole_difference (-1327/200) c2_1 c2_2 c2_3 c2_4 (2254/1727)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have hq := quadratic_A f g
  unfold mass F1FreshFTC.AOne.primitive collected rational
  linear_combination h0+h1+h2+hq
end AOne

namespace ATwo
open F1FreshFTC.ATwo
def rational : ℝ := poleR (0) c0_2 c0_3 c0_4+
  poleR (-1327/200) c1_2 c1_3 c1_4+
  poleR (1) c2_2 c2_3 c2_4+
  poleR (2/3) c3_2 c3_3 c3_4+p0*(927/200-2)+(p1/2)*((927/200)^2-2^2)

def collected : ℝ := c0_1*log (927/400)+
  c1_1*log (2254/1727)+
  c2_1*log (727/200)+
  c3_1*log (refTwo)+
  (f/21)*log refTwo+tMinus f g*log crossTwoMinus-tPlus f g*log crossTwoPlus+rational

theorem collected_exact : mass = collected := by
  have h0 := pole_difference (0) c0_1 c0_2 c0_3 c0_4 (927/400)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h1 := pole_difference (-1327/200) c1_1 c1_2 c1_3 c1_4 (2254/1727)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h2 := pole_difference (1) c2_1 c2_2 c2_3 c2_4 (727/200)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h3 := pole_difference (2/3) c3_1 c3_2 c3_3 c3_4 (refTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have hq := quadratic_T f g
  unfold mass F1FreshFTC.ATwo.primitive collected rational
  linear_combination h0+h1+h2+h3+hq
end ATwo

namespace BOne
open F1FreshFTC.BOne
def rational : ℝ := poleR (-2) c0_2 c0_3 c0_4+
  poleR (2/3) c1_2 c1_3 c1_4+
  poleR (-1327/200) c2_2 c2_3 c2_4+
  poleR (-1727/600) c3_2 c3_3 c3_4+p0*(927/200-2)+(p1/2)*((927/200)^2-2^2)

def collected : ℝ := c0_1*log (refOne)+
  c1_1*log (refTwo)+
  c2_1*log (2254/1727)+
  c3_1*log (bRefOne)+
  (f/21)*log bRefOne+bMinus f g*log bCrossOneMinus-bPlus f g*log bCrossOnePlus+rational

theorem collected_exact : mass = collected := by
  have h0 := pole_difference (-2) c0_1 c0_2 c0_3 c0_4 (refOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h1 := pole_difference (2/3) c1_1 c1_2 c1_3 c1_4 (refTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h2 := pole_difference (-1327/200) c2_1 c2_2 c2_3 c2_4 (2254/1727)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h3 := pole_difference (-1727/600) c3_1 c3_2 c3_3 c3_4 (bRefOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have hq := quadratic_B f g
  unfold mass F1FreshFTC.BOne.primitive collected rational
  linear_combination h0+h1+h2+h3+hq
end BOne

namespace BTwo
open F1FreshFTC.BTwo
def rational : ℝ := poleR (-2) c0_2 c0_3 c0_4+
  poleR (2/3) c1_2 c1_3 c1_4+
  poleR (-3581/200) c2_2 c2_3 c2_4+p0*(927/200-2)+(p1/2)*((927/200)^2-2^2)

def collected : ℝ := c0_1*log (refOne)+
  c1_1*log (refTwo)+
  c2_1*log (bRefTwo)+
  (f)*log bRefTwo+dMinus f g*log bCrossTwoMinus-dPlus f g*log bCrossTwoPlus+rational

theorem collected_exact : mass = collected := by
  have h0 := pole_difference (-2) c0_1 c0_2 c0_3 c0_4 (refOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h1 := pole_difference (2/3) c1_1 c1_2 c1_3 c1_4 (refTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h2 := pole_difference (-3581/200) c2_1 c2_2 c2_3 c2_4 (bRefTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have hq := quadratic_D f g
  unfold mass F1FreshFTC.BTwo.primitive collected rational
  linear_combination h0+h1+h2+hq
end BTwo
end FreshLogEndpoints

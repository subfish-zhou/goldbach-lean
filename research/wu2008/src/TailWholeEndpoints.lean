import ActualTailFinite

noncomputable section
open Real F1JointFTC F1ActualSecondFTC F1BFullFTC FreshLogBasis
namespace TailWholeEndpoints

namespace AB11
open TailFiniteFTC.AB11

def rational : ℝ := poleR (0) c0_2 c0_3 c0_4+
  poleR (-2) c2_2 c2_3 c2_4+
  poleR (-1327/200) c4_2 c4_3 c4_4+
  poleR (-1727/600) c5_2 c5_3 c5_4+
  (TailRationalBasis.fifthPrimitive 0 c0_5 (927/200)-TailRationalBasis.fifthPrimitive 0 c0_5 2)

def collected : ℝ := c0_1*log (927/400)+
  c2_1*log (refOne)+
  c4_1*log (2254/1727)+
  c5_1*log (bRefOne)+
  f0*log refOne+aMinus f0 g0*log crossOneMinus-aPlus f0 g0*log crossOnePlus+
  (f2/21)*log bRefOne+bMinus f2 g2*log bCrossOneMinus-bPlus f2 g2*log bCrossOnePlus+
  rational

theorem collected_exact : mass=collected := by
  have h0 := pole_difference (0) c0_1 c0_2 c0_3 c0_4 (927/400)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h2 := pole_difference (-2) c2_1 c2_2 c2_3 c2_4 (refOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h4 := pole_difference (-1327/200) c4_1 c4_2 c4_3 c4_4 (2254/1727)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h5 := pole_difference (-1727/600) c5_1 c5_2 c5_3 c5_4 (bRefOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have q0 := quadratic_A f0 g0
  have q2 := quadratic_B f2 g2
  unfold mass TailFiniteFTC.AB11.primitive collected rational
  linear_combination h0+h2+h4+h5+q0+q2
end AB11

namespace AB12
open TailFiniteFTC.AB12

def rational : ℝ := poleR (0) c0_2 c0_3 c0_4+
  poleR (-2) c2_2 c2_3 c2_4+
  poleR (-3581/200) c6_2 c6_3 c6_4+
  (TailRationalBasis.fifthPrimitive 0 c0_5 (927/200)-TailRationalBasis.fifthPrimitive 0 c0_5 2)

def collected : ℝ := c0_1*log (927/400)+
  c2_1*log (refOne)+
  c6_1*log (bRefTwo)+
  f0*log refOne+aMinus f0 g0*log crossOneMinus-aPlus f0 g0*log crossOnePlus+
  f3*log bRefTwo+dMinus f3 g3*log bCrossTwoMinus-dPlus f3 g3*log bCrossTwoPlus+
  rational

theorem collected_exact : mass=collected := by
  have h0 := pole_difference (0) c0_1 c0_2 c0_3 c0_4 (927/400)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h2 := pole_difference (-2) c2_1 c2_2 c2_3 c2_4 (refOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h6 := pole_difference (-3581/200) c6_1 c6_2 c6_3 c6_4 (bRefTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have q0 := quadratic_A f0 g0
  have q3 := quadratic_D f3 g3
  unfold mass TailFiniteFTC.AB12.primitive collected rational
  linear_combination h0+h2+h6+q0+q3
end AB12

namespace AB21
open TailFiniteFTC.AB21

def rational : ℝ := poleR (1) c1_2 c1_3 c1_4+
  poleR (2/3) c3_2 c3_3 c3_4+
  poleR (-1327/200) c4_2 c4_3 c4_4+
  poleR (-1727/600) c5_2 c5_3 c5_4

def collected : ℝ := c1_1*log (727/200)+
  c3_1*log (refTwo)+
  c4_1*log (2254/1727)+
  c5_1*log (bRefOne)+
  (f1/21)*log refTwo+tMinus f1 g1*log crossTwoMinus-tPlus f1 g1*log crossTwoPlus+
  (f2/21)*log bRefOne+bMinus f2 g2*log bCrossOneMinus-bPlus f2 g2*log bCrossOnePlus+
  rational

theorem collected_exact : mass=collected := by
  have h1 := pole_difference (1) c1_1 c1_2 c1_3 c1_4 (727/200)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h3 := pole_difference (2/3) c3_1 c3_2 c3_3 c3_4 (refTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h4 := pole_difference (-1327/200) c4_1 c4_2 c4_3 c4_4 (2254/1727)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h5 := pole_difference (-1727/600) c5_1 c5_2 c5_3 c5_4 (bRefOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have q1 := quadratic_T f1 g1
  have q2 := quadratic_B f2 g2
  unfold mass TailFiniteFTC.AB21.primitive collected rational
  linear_combination h1+h3+h4+h5+q1+q2
end AB21

namespace AB22
open TailFiniteFTC.AB22

def rational : ℝ := poleR (1) c1_2 c1_3 c1_4+
  poleR (2/3) c3_2 c3_3 c3_4+
  poleR (-3581/200) c6_2 c6_3 c6_4+
  (p0/1)*((927/200)^1-2^1)+
  (p1/2)*((927/200)^2-2^2)

def collected : ℝ := c1_1*log (727/200)+
  c3_1*log (refTwo)+
  c6_1*log (bRefTwo)+
  (f1/21)*log refTwo+tMinus f1 g1*log crossTwoMinus-tPlus f1 g1*log crossTwoPlus+
  f3*log bRefTwo+dMinus f3 g3*log bCrossTwoMinus-dPlus f3 g3*log bCrossTwoPlus+
  rational

theorem collected_exact : mass=collected := by
  have h1 := pole_difference (1) c1_1 c1_2 c1_3 c1_4 (727/200)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h3 := pole_difference (2/3) c3_1 c3_2 c3_3 c3_4 (refTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h6 := pole_difference (-3581/200) c6_1 c6_2 c6_3 c6_4 (bRefTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have q1 := quadratic_T f1 g1
  have q3 := quadratic_D f3 g3
  unfold mass TailFiniteFTC.AB22.primitive collected rational
  linear_combination h1+h3+h6+q1+q3
end AB22

namespace BA11
open TailFiniteFTC.BA11

def rational : ℝ := poleR (0) c0_2 c0_3 c0_4+
  poleR (-2) c2_2 c2_3 c2_4+
  poleR (-1327/200) c4_2 c4_3 c4_4+
  poleR (-1727/600) c5_2 c5_3 c5_4

def collected : ℝ := c0_1*log (927/400)+
  c2_1*log (refOne)+
  c4_1*log (2254/1727)+
  c5_1*log (bRefOne)+
  f0*log refOne+aMinus f0 g0*log crossOneMinus-aPlus f0 g0*log crossOnePlus+
  (f2/21)*log bRefOne+bMinus f2 g2*log bCrossOneMinus-bPlus f2 g2*log bCrossOnePlus+
  rational

theorem collected_exact : mass=collected := by
  have h0 := pole_difference (0) c0_1 c0_2 c0_3 c0_4 (927/400)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h2 := pole_difference (-2) c2_1 c2_2 c2_3 c2_4 (refOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h4 := pole_difference (-1327/200) c4_1 c4_2 c4_3 c4_4 (2254/1727)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h5 := pole_difference (-1727/600) c5_1 c5_2 c5_3 c5_4 (bRefOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have q0 := quadratic_A f0 g0
  have q2 := quadratic_B f2 g2
  unfold mass TailFiniteFTC.BA11.primitive collected rational
  linear_combination h0+h2+h4+h5+q0+q2
end BA11

namespace BA12
open TailFiniteFTC.BA12

def rational : ℝ := poleR (0) c0_2 c0_3 c0_4+
  poleR (-2) c2_2 c2_3 c2_4+
  poleR (-3581/200) c6_2 c6_3 c6_4+
  (p0/1)*((927/200)^1-2^1)+
  (p1/2)*((927/200)^2-2^2)+
  (p2/3)*((927/200)^3-2^3)+
  (p3/4)*((927/200)^4-2^4)

def collected : ℝ := c0_1*log (927/400)+
  c2_1*log (refOne)+
  c6_1*log (bRefTwo)+
  f0*log refOne+aMinus f0 g0*log crossOneMinus-aPlus f0 g0*log crossOnePlus+
  f3*log bRefTwo+dMinus f3 g3*log bCrossTwoMinus-dPlus f3 g3*log bCrossTwoPlus+
  rational

theorem collected_exact : mass=collected := by
  have h0 := pole_difference (0) c0_1 c0_2 c0_3 c0_4 (927/400)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h2 := pole_difference (-2) c2_1 c2_2 c2_3 c2_4 (refOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h6 := pole_difference (-3581/200) c6_1 c6_2 c6_3 c6_4 (bRefTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have q0 := quadratic_A f0 g0
  have q3 := quadratic_D f3 g3
  unfold mass TailFiniteFTC.BA12.primitive collected rational
  linear_combination h0+h2+h6+q0+q3
end BA12

namespace BA21
open TailFiniteFTC.BA21

def rational : ℝ := poleR (0) c0_2 c0_3 c0_4+
  poleR (1) c1_2 c1_3 c1_4+
  poleR (2/3) c3_2 c3_3 c3_4+
  poleR (-1327/200) c4_2 c4_3 c4_4+
  poleR (-1727/600) c5_2 c5_3 c5_4

def collected : ℝ := c0_1*log (927/400)+
  c1_1*log (727/200)+
  c3_1*log (refTwo)+
  c4_1*log (2254/1727)+
  c5_1*log (bRefOne)+
  (f1/21)*log refTwo+tMinus f1 g1*log crossTwoMinus-tPlus f1 g1*log crossTwoPlus+
  (f2/21)*log bRefOne+bMinus f2 g2*log bCrossOneMinus-bPlus f2 g2*log bCrossOnePlus+
  rational

theorem collected_exact : mass=collected := by
  have h0 := pole_difference (0) c0_1 c0_2 c0_3 c0_4 (927/400)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h1 := pole_difference (1) c1_1 c1_2 c1_3 c1_4 (727/200)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h3 := pole_difference (2/3) c3_1 c3_2 c3_3 c3_4 (refTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h4 := pole_difference (-1327/200) c4_1 c4_2 c4_3 c4_4 (2254/1727)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h5 := pole_difference (-1727/600) c5_1 c5_2 c5_3 c5_4 (bRefOne)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have q1 := quadratic_T f1 g1
  have q2 := quadratic_B f2 g2
  unfold mass TailFiniteFTC.BA21.primitive collected rational
  linear_combination h0+h1+h3+h4+h5+q1+q2
end BA21

namespace BA22
open TailFiniteFTC.BA22

def rational : ℝ := poleR (0) c0_2 c0_3 c0_4+
  poleR (1) c1_2 c1_3 c1_4+
  poleR (2/3) c3_2 c3_3 c3_4+
  poleR (-3581/200) c6_2 c6_3 c6_4+
  (p0/1)*((927/200)^1-2^1)+
  (p1/2)*((927/200)^2-2^2)+
  (p2/3)*((927/200)^3-2^3)+
  (p3/4)*((927/200)^4-2^4)

def collected : ℝ := c0_1*log (927/400)+
  c1_1*log (727/200)+
  c3_1*log (refTwo)+
  c6_1*log (bRefTwo)+
  (f1/21)*log refTwo+tMinus f1 g1*log crossTwoMinus-tPlus f1 g1*log crossTwoPlus+
  f3*log bRefTwo+dMinus f3 g3*log bCrossTwoMinus-dPlus f3 g3*log bCrossTwoPlus+
  rational

theorem collected_exact : mass=collected := by
  have h0 := pole_difference (0) c0_1 c0_2 c0_3 c0_4 (927/400)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h1 := pole_difference (1) c1_1 c1_2 c1_3 c1_4 (727/200)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h3 := pole_difference (2/3) c3_1 c3_2 c3_3 c3_4 (refTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have h6 := pole_difference (-3581/200) c6_1 c6_2 c6_3 c6_4 (bRefTwo)
    (by norm_num) (by norm_num [refOne,refTwo,bRefOne,bRefTwo])
  have q1 := quadratic_T f1 g1
  have q3 := quadratic_D f3 g3
  unfold mass TailFiniteFTC.BA22.primitive collected rational
  linear_combination h0+h1+h3+h6+q1+q3
end BA22

end TailWholeEndpoints

import WR2XiSixthCompactPanel
import WR2XiSixthPayments

/-! Direct exact-rational checking of the unchanged sixth-source payments.
The intermediate rounded density and profile certificates are unnecessary:
their product is bounded directly, using the same analytic panel lemma. -/
namespace WuPaper.R2Xi.SixthContinuous.DirectCheck
open QuarterTrim NodeExtension SourceRational WuSource.SrcSixthGain

def logLower (t : ℚ) : ℚ :=
  let z := (t-1)/(t+1)
  2*(z+z^3/3+z^5/5+z^7/7)
def node (k : ℕ) : ℚ := 2+k/10
def left (k : ℕ) : ℚ := if k = 2 then 1 else node (k-1)
def weight : ℕ → ℚ
  | 2 => 22266/1000000 | 3 => 21591/1000000 | 4 => 20159/1000000
  | 5 => 18016/1000000 | 6 => 15756/1000000 | 7 => 12894/1000000
  | 8 => 9961/1000000 | 9 => 7682/1000000 | 10 => 7139/1000000
  | k => upperNumerator k/10000000000
def low (z : ℚ) : ℚ := max (100/1327) (z-1/4)
def up (z : ℚ) : ℚ := min (25/206) (z-25/206)
def ratio (a b : ℚ) : ℚ :=
  let za := 1/2-(100/1327)*a
  let zb := 1/2-(100/1327)*b
  up zb*(zb-low zb)/(low za*(za-up za))
def density (a b : ℚ) : ℚ :=
  logLower (max 1 (ratio a b))/(b*(1-2*(100/1327)*a))
def profile (k : ℕ) (b : ℚ) : ℚ :=
  weight k*logLower (node k/(b-1))+tailNumerator k/1000000000000
def point (i : ℕ) : ℚ := 2+(41453/10300-2)*i/1024
/-- The least available profile interval containing the panel's right endpoint. -/
def index (i : ℕ) : ℕ := max 2 ((208530*(i+1)-105472000+10547199)/10547200)
def condition (i : ℕ) : Prop :=
  let a := point i
  let b := point (i+1)
  let k := index i
  2 ≤ a ∧ a ≤ b ∧ b ≤ 41453/10300 ∧
  2 ≤ k ∧ k ≤ 11 ∧ left k ≤ b-1 ∧ b-1 ≤ node k ∧
  0 ≤ profile k b ∧
  paymentNumerator i/1000000000000 ≤ 8*(b-a)*(density a b*profile k b)
instance (i : ℕ) : Decidable (condition i) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem cast_logLower (t : ℚ) :
    (logLower t : ℝ) = SourceLogRational.lower t := by
  simp [logLower, SourceLogRational.lower]
@[simp] theorem cast_node (k : ℕ) : (node k : ℝ) = rNode k := by
  simp [node, rNode]
@[simp] theorem cast_left (k : ℕ) : (left k : ℝ) = profileLeft k := by
  by_cases h : k = 2 <;> simp [left, profileLeft, h]
theorem cast_weight {k : ℕ} (hk : 2 ≤ k) (hk11 : k ≤ 11) :
    (weight k : ℝ) = upperLower k := by
  interval_cases k <;> norm_num [weight,upperLower,upperNumerator,RationalCandidate.lowerH]
@[simp] theorem cast_low (z : ℚ) : (low z : ℝ) = lowerX z := by
  simp [low,lowerX,alpha]
@[simp] theorem cast_up (z : ℚ) : (up z : ℝ) = upperX z := by
  simp [up,upperX,beta]
@[simp] theorem cast_ratio (a b : ℚ) : (ratio a b : ℝ) = panelRatio a b := by
  simp [ratio,panelRatio,alpha]
@[simp] theorem cast_density (a b : ℚ) : (density a b : ℝ) = densityLower a b := by
  simp [density,densityLower,alpha]
@[simp] theorem cast_point (i : ℕ) : (point i : ℝ) = grid i := by
  simp [point,grid]
theorem cast_profile {k : ℕ} (hk : 2 ≤ k) (hk11 : k ≤ 11) (b : ℚ) :
    (profile k b : ℝ) = upperLower k*SourceLogRational.lower (rNode k/(b-1))+
      (tailNumerator k:ℝ)/1000000000000 := by
  simp [profile,cast_weight hk hk11]

/-- Soundness is analytic; each instance only checks exact rational inequalities. -/
theorem condition_sound {i : ℕ} (h : condition i) : payment i ≤ panelBound i := by
  obtain ⟨ha,hab,hb,hk,hk11,hs0,hs1,hp,hq⟩ := h
  have ha' := (Rat.cast_le (K := ℝ)).mpr ha
  have hab' := (Rat.cast_le (K := ℝ)).mpr hab
  have hb' := (Rat.cast_le (K := ℝ)).mpr hb
  have hs0' := (Rat.cast_le (K := ℝ)).mpr hs0
  have hs1' := (Rat.cast_le (K := ℝ)).mpr hs1
  have hp' := (Rat.cast_le (K := ℝ)).mpr hp
  have hq' := (Rat.cast_le (K := ℝ)).mpr hq
  simp only [Rat.cast_ofNat,cast_point] at ha' hab'
  have hend : ((41453/10300:ℚ):ℝ) = endpoint := by norm_num [endpoint,alpha,beta]
  rw [cast_point,hend] at hb'
  simp only [Rat.cast_sub,Rat.cast_one,cast_left,cast_point,cast_node] at hs0' hs1'
  simp only [Rat.cast_zero] at hp'
  apply compact_panel_paid ha' hab' hb' hk hk11 hs0' hs1' hp'
    (p := (profile (index i) (point (i+1)):ℝ)) (d := (density (point i) (point (i+1)):ℝ))
  · simpa only [cast_point] using le_of_eq (cast_profile hk hk11 (point (i+1)))
  · simpa only [cast_point] using le_of_eq (cast_density (point i) (point (i+1)))
  · simpa [payment,panelBound] using hq'

end WuPaper.R2Xi.SixthContinuous.DirectCheck
#print axioms WuPaper.R2Xi.SixthContinuous.DirectCheck.condition_sound

import SigmaCorrectionSignedAtoms
namespace SigmaCorrectionFTC
open Real OriginalSigmaStrength
noncomputable section

def hermiteA : ℝ := 341200/3969
def hermiteB : ℝ := 426800/3969
def fullQBOne : ℝ := 192265748240/19931774247
def fullQBZero : ℝ := 59683530320/6643924749
def fullRational (t : ℝ) : ℝ := (hermiteA*t+hermiteB)/qB t

/-- Old endpoint payment plus actual correction, with common poles collected before any log bounds. -/
def fullPrimitive (t : ℝ) : ℝ :=
  poleFourPrimitive (0) (23459573759494777727/159040724270459062500) (-7668814423/91965608043750) (2914132/179480109375) (-44/28021875) t+
  poleFourPrimitive (1) (-4/35) (0) (0) (0) t+
  poleFourPrimitive (2) (-3/20) (0) (0) (0) t+
  poleFourPrimitive (3) (-36416/76545) (-2432/25515) (512/1701) (1024/2835) t+
  poleFourPrimitive (5) (26940087976/24020390625) (37444664/145578125) (-41190048/13234375) (-1134432/240625) t+
  poleFourPrimitive (5/3) (-37120077824/45581484375) (759382016/3906984375) (-276955136/1674421875) (4456448/143521875) t+
  quadraticAPrimitive (-7903489340/2035338627) (6526017140/2035338627) t+
  fullRational t+SigmaInnerPaid.quadraticPrimitive fullQBOne fullQBZero t

theorem fullPrimitive_identity (t : ℝ) :
    fullPrimitive t=SigmaInnerPaid.primitive t+primitive t := by
  unfold fullPrimitive SigmaInnerPaid.primitive primitive repeatedPrimitive
    poleFourPrimitive polePrimitive fullRational hermiteA hermiteB fullQBOne fullQBZero
    SigmaInnerPaid.quadraticPrimitive F1JointFTC.quadraticPrimitive qB
  simp only [add_zero,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Signed finite ledger of the fully collected primitive; all repeated-pole rational terms retained. -/
def fullCellPaid (a b : ℝ) : ℝ :=
  poleFourPaid (0) (23459573759494777727/159040724270459062500) (-7668814423/91965608043750) (2914132/179480109375) (-44/28021875) a b+
  poleFourPaid (1) (-4/35) (0) (0) (0) a b+
  poleFourPaid (2) (-3/20) (0) (0) (0) a b+
  poleFourPaid (3) (-36416/76545) (-2432/25515) (512/1701) (1024/2835) a b+
  poleFourPaid (5) (26940087976/24020390625) (37444664/145578125) (-41190048/13234375) (-1134432/240625) a b+
  poleFourPaid (5/3) (-37120077824/45581484375) (759382016/3906984375) (-276955136/1674421875) (4456448/143521875) a b+
  quadraticAPaid (-7903489340/2035338627) (6526017140/2035338627) a b+
  (fullRational b-fullRational a)+quadraticBPaid fullQBOne fullQBZero a b

theorem fullCellPaid_le {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    fullCellPaid a b≤fullPrimitive b-fullPrimitive a := by
  have h0 := poleFourPaid_le (0) (23459573759494777727/159040724270459062500) (-7668814423/91965608043750) (2914132/179480109375) (-44/28021875) (by linarith : 0<a+0) hab
  have h1 := poleFourPaid_le (1) (-4/35) (0) (0) (0) (by linarith : 0<a+1) hab
  have h2 := poleFourPaid_le (2) (-3/20) (0) (0) (0) (by linarith : 0<a+2) hab
  have h3 := poleFourPaid_le (3) (-36416/76545) (-2432/25515) (512/1701) (1024/2835) (by linarith : 0<a+3) hab
  have h4 := poleFourPaid_le (5) (26940087976/24020390625) (37444664/145578125) (-41190048/13234375) (-1134432/240625) (by linarith : 0<a+5) hab
  have h5 := poleFourPaid_le (5/3) (-37120077824/45581484375) (759382016/3906984375) (-276955136/1674421875) (4456448/143521875) (by linarith : 0<a+5/3) hab
  have hA := quadraticAPaid_le (-7903489340/2035338627) (6526017140/2035338627) ha hab
  have hB := quadraticBPaid_le fullQBOne fullQBZero ha hab
  unfold fullCellPaid fullPrimitive
  linarith only [h0,h1,h2,h3,h4,h5,hA,hB]

end
end SigmaCorrectionFTC

import Hf4TargetConstants

noncomputable section
namespace Hf4Quad

structure Cubic where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def Cubic.eval (p : Cubic) (x : ℝ) : ℝ := p.a+p.b*x+p.c*x^2+p.d*x^3

def Cubic.norm (p : Cubic) : ℝ := |p.a|+|p.b|+|p.c|+|p.d|

def Model (f : ℝ → ℝ) (p : Cubic) (e : ℝ) : Prop :=
  ∀ x : ℝ, |x| ≤ 1 → |f x-p.eval x| ≤ e

theorem abs_monomial (a x : ℝ) (n : ℕ) (hx : |x| ≤ 1) : |a*x^n| ≤ |a| := by
  rw [abs_mul, abs_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hx) (abs_nonneg a)).trans_eq (mul_one _)

theorem abs_poly6 (a b c d e f g x : ℝ) (hx : |x| ≤ 1) :
    |a+b*x+c*x^2+d*x^3+e*x^4+f*x^5+g*x^6| ≤
      |a|+|b|+|c|+|d|+|e|+|f|+|g| := by
  have hb : |b*x| ≤ |b| := by simpa using abs_monomial b x 1 hx
  have hc := abs_monomial c x 2 hx
  have hd := abs_monomial d x 3 hx
  have he := abs_monomial e x 4 hx
  have hf := abs_monomial f x 5 hx
  have hg := abs_monomial g x 6 hx
  calc
    _ ≤ |a+b*x+c*x^2+d*x^3+e*x^4+f*x^5|+|g*x^6| := abs_add_le _ _
    _ ≤ (|a+b*x+c*x^2+d*x^3+e*x^4|+|f*x^5|)+|g*x^6| := by gcongr; exact abs_add_le _ _
    _ ≤ ((|a+b*x+c*x^2+d*x^3|+|e*x^4|)+|f*x^5|)+|g*x^6| := by gcongr; exact abs_add_le _ _
    _ ≤ (((|a+b*x+c*x^2|+|d*x^3|)+|e*x^4|)+|f*x^5|)+|g*x^6| := by gcongr; exact abs_add_le _ _
    _ ≤ ((((|a+b*x|+|c*x^2|)+|d*x^3|)+|e*x^4|)+|f*x^5|)+|g*x^6| := by gcongr; exact abs_add_le _ _
    _ ≤ (((((|a|+|b*x|)+|c*x^2|)+|d*x^3|)+|e*x^4|)+|f*x^5|)+|g*x^6| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith only [hb,hc,hd,he,hf,hg]

theorem Cubic.abs_eval (p : Cubic) (x : ℝ) (hx : |x| ≤ 1) : |p.eval x| ≤ p.norm := by
  simpa [Cubic.eval,Cubic.norm] using abs_poly6 p.a p.b p.c p.d 0 0 0 x hx

def mulError (p q r : Cubic) : ℝ :=
  |p.a*q.a-r.a|+|p.a*q.b+p.b*q.a-r.b|+
  |p.a*q.c+p.b*q.b+p.c*q.a-r.c|+
  |p.a*q.d+p.b*q.c+p.c*q.b+p.d*q.a-r.d|+
  |p.b*q.d+p.c*q.c+p.d*q.b|+|p.c*q.d+p.d*q.c|+|p.d*q.d|

theorem mul_residual (p q r : Cubic) (x : ℝ) (hx : |x| ≤ 1) :
    |p.eval x*q.eval x-r.eval x| ≤ mulError p q r := by
  have he : p.eval x*q.eval x-r.eval x =
      (p.a*q.a-r.a)+(p.a*q.b+p.b*q.a-r.b)*x+
      (p.a*q.c+p.b*q.b+p.c*q.a-r.c)*x^2+
      (p.a*q.d+p.b*q.c+p.c*q.b+p.d*q.a-r.d)*x^3+
      (p.b*q.d+p.c*q.c+p.d*q.b)*x^4+(p.c*q.d+p.d*q.c)*x^5+
      (p.d*q.d)*x^6 := by simp only [Cubic.eval]; ring
  rw [he]
  exact abs_poly6 _ _ _ _ _ _ _ x hx

theorem Model.nonneg {f : ℝ → ℝ} {p : Cubic} {e : ℝ} (h : Model f p e) : 0 ≤ e :=
  (abs_nonneg _).trans (h 0 (by norm_num))

theorem Model.exact (p : Cubic) : Model p.eval p 0 := by
  intro x _
  simp

theorem Model.widen {f : ℝ → ℝ} {p q : Cubic} {e E : ℝ}
    (h : Model f p e) (hE : e+|p.a-q.a|+|p.b-q.b|+|p.c-q.c|+|p.d-q.d| ≤ E) :
    Model f q E := by
  intro x hx
  have hpq : |p.eval x-q.eval x| ≤ |p.a-q.a|+|p.b-q.b|+|p.c-q.c|+|p.d-q.d| := by
    have hh := (Cubic.abs_eval (⟨p.a-q.a,p.b-q.b,p.c-q.c,p.d-q.d⟩ : Cubic) x hx)
    convert hh using 1
    · congr 1
      simp only [Cubic.eval]
      ring
    · rfl
  have hh := abs_add_le (f x-p.eval x) (p.eval x-q.eval x)
  rw [sub_add_sub_cancel] at hh
  linarith only [hh,h x hx,hpq,hE]

theorem Model.add {f g : ℝ → ℝ} {p q r : Cubic} {e d E : ℝ}
    (hf : Model f p e) (hg : Model g q d)
    (hE : e+d+|p.a+q.a-r.a|+|p.b+q.b-r.b|+|p.c+q.c-r.c|+|p.d+q.d-r.d| ≤ E) :
    Model (fun x => f x+g x) r E := by
  apply Model.widen (p := ⟨p.a+q.a,p.b+q.b,p.c+q.c,p.d+q.d⟩) (e := e+d) _ hE
  intro x hx
  have he : f x+g x-(Cubic.eval ⟨p.a+q.a,p.b+q.b,p.c+q.c,p.d+q.d⟩ x) =
      (f x-p.eval x)+(g x-q.eval x) := by simp only [Cubic.eval]; ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (hf x hx) (hg x hx))

theorem Model.mul {f g : ℝ → ℝ} {p q r : Cubic} {e d E : ℝ}
    (hf : Model f p e) (hg : Model g q d)
    (hE : e*q.norm+d*p.norm+e*d+mulError p q r ≤ E) :
    Model (fun x => f x*g x) r E := by
  intro x hx
  have he : f x*g x-r.eval x =
      (f x-p.eval x)*q.eval x+(g x-q.eval x)*p.eval x+
      (f x-p.eval x)*(g x-q.eval x)+(p.eval x*q.eval x-r.eval x) := by ring
  rw [he]
  have h1 : |(f x-p.eval x)*q.eval x| ≤ e*q.norm := by
    rw [abs_mul]
    exact mul_le_mul (hf x hx) (q.abs_eval x hx) (abs_nonneg _) hf.nonneg
  have h2 : |(g x-q.eval x)*p.eval x| ≤ d*p.norm := by
    rw [abs_mul]
    exact mul_le_mul (hg x hx) (p.abs_eval x hx) (abs_nonneg _) hg.nonneg
  have h3 : |(f x-p.eval x)*(g x-q.eval x)| ≤ e*d := by
    rw [abs_mul]
    exact mul_le_mul (hf x hx) (hg x hx) (abs_nonneg _) hf.nonneg
  calc
    _ ≤ |(f x-p.eval x)*q.eval x+(g x-q.eval x)*p.eval x+
      (f x-p.eval x)*(g x-q.eval x)|+|p.eval x*q.eval x-r.eval x| := abs_add_le _ _
    _ ≤ (|(f x-p.eval x)*q.eval x+(g x-q.eval x)*p.eval x|+
      |(f x-p.eval x)*(g x-q.eval x)|)+|p.eval x*q.eval x-r.eval x| := by gcongr; exact abs_add_le _ _
    _ ≤ ((|(f x-p.eval x)*q.eval x|+|(g x-q.eval x)*p.eval x|)+
      |(f x-p.eval x)*(g x-q.eval x)|)+|p.eval x*q.eval x-r.eval x| := by gcongr; exact abs_add_le _ _
    _ ≤ E := by linarith only [h1,h2,h3,mul_residual p q r x hx,hE]

theorem Model.inv {f : ℝ → ℝ} {p q : Cubic} {e L E : ℝ}
    (hf : Model f p e) (hL : 0 < L)
    (hlower : L ≤ |p.a|-|p.b|-|p.c|-|p.d|-e)
    (hE : mulError p q ⟨1,0,0,0⟩+q.norm*e ≤ L*E) :
    Model (fun x => (f x)⁻¹) q E := by
  intro x hx
  have ht : |p.eval x-p.a| ≤ |p.b|+|p.c|+|p.d| := by
    have hh := (Cubic.abs_eval (⟨0,p.b,p.c,p.d⟩ : Cubic) x hx)
    have he : p.eval x-p.a = (Cubic.eval ⟨0,p.b,p.c,p.d⟩ x) := by
      simp only [Cubic.eval]
      ring
    rw [he]
    simpa [Cubic.norm] using hh
  have hl : L ≤ |f x| := by
    have h := abs_sub_abs_le_abs_sub p.a (p.eval x)
    have ha := abs_sub_abs_le_abs_sub (p.eval x) (f x)
    rw [abs_sub_comm p.a] at h
    rw [abs_sub_comm (p.eval x)] at ha
    linarith only [h,ha,ht,hf x hx,hlower]
  have hn : f x ≠ 0 := abs_pos.mp (hL.trans_le hl)
  have hres : |1-f x*q.eval x| ≤ mulError p q ⟨1,0,0,0⟩+q.norm*e := by
    have he : 1-f x*q.eval x = -(p.eval x*q.eval x-1)-q.eval x*(f x-p.eval x) := by ring
    rw [he]
    have hh : |q.eval x*(f x-p.eval x)| ≤ q.norm*e := by
      rw [abs_mul]
      exact mul_le_mul (q.abs_eval x hx) (hf x hx) (abs_nonneg _)
        (by unfold Cubic.norm; positivity)
    have hr := mul_residual p q ⟨1,0,0,0⟩ x hx
    simp only [Cubic.eval,zero_mul,add_zero] at hr
    calc
      _ ≤ |-(p.eval x*q.eval x-1)|+|q.eval x*(f x-p.eval x)| := by
        simpa only [sub_eq_add_neg,abs_neg] using
          abs_add_le (-(p.eval x*q.eval x-1)) (-(q.eval x*(f x-p.eval x)))
      _ ≤ _ := by rw [abs_neg]; exact add_le_add hr hh
  have hE0 : 0 ≤ E := by
    have hnn : 0 ≤ mulError p q ⟨1,0,0,0⟩+q.norm*e := (abs_nonneg _).trans hres
    nlinarith only [hE,hnn,hL]
  have he : (f x)⁻¹-q.eval x = (1-f x*q.eval x)/f x := by field_simp
  rw [he,abs_div]
  apply (div_le_iff₀ (hL.trans_le hl)).mpr
  exact hres.trans (hE.trans (by nlinarith only [hl,hE0]))

end Hf4Quad

import MathlibNt.SieveTheory.LiLiuGoldbachS3PolynomialData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
# Exact coefficient operations for the S3 integral certificate

Coefficients are rational and listed from constant term upwards, as in
`s3eval`. The evaluation lemmas let finite coefficient equalities replace
large symbolic expansions over the reals. Numerical certificates are checked
by Lean's kernel, without native evaluation axioms.
-/

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace S3Polynomial

def add : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => (x+y)::add xs ys

def scale (c : ℚ) : List ℚ → List ℚ := List.map (c * ·)

def mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | _, [] => []
  | c::cs, d::ds => add (scale c (d::ds)) (0::mul cs (d::ds))

def translate (a : ℚ) : List ℚ → List ℚ
  | [] => []
  | c::cs => add [c] (mul [a,1] (translate a cs))

theorem eval_add (cs ds : List ℚ) (x : ℝ) :
    s3eval (add cs ds) x = s3eval cs x + s3eval ds x := by
  induction cs generalizing ds with
  | nil => simp [add,s3eval]
  | cons c cs ih =>
    cases ds with
    | nil => simp [add,s3eval]
    | cons d ds => simp [add,s3eval,ih]; ring

theorem eval_scale (c : ℚ) (cs : List ℚ) (x : ℝ) :
    s3eval (scale c cs) x = (c : ℝ)*s3eval cs x := by
  induction cs with
  | nil => simp [scale,s3eval]
  | cons d ds ih => simp [scale,s3eval] at ih ⊢; rw [ih]; ring

theorem eval_mul (cs ds : List ℚ) (x : ℝ) :
    s3eval (mul cs ds) x = s3eval cs x * s3eval ds x := by
  induction cs with
  | nil => simp [mul,s3eval]
  | cons c cs ih =>
    cases ds with
    | nil => simp [mul,s3eval]
    | cons d ds => rw [mul,eval_add,eval_scale]; simp only [s3eval,ih]; ring

theorem eval_translate (a : ℚ) (cs : List ℚ) (x : ℝ) :
    s3eval (translate a cs) x = s3eval cs ((a : ℝ)+x) := by
  induction cs with
  | nil => simp [translate,s3eval]
  | cons c cs ih =>
    rw [translate,eval_add,eval_mul,ih]
    simp [s3eval]

def monomial (n : ℕ) (c : ℚ) : List ℚ := List.replicate n 0 ++ [c]

def sumRange (f : ℕ → List ℚ) : ℕ → List ℚ
  | 0 => []
  | n+1 => add (sumRange f n) (f n)

theorem eval_monomial (n : ℕ) (c : ℚ) (x : ℝ) :
    s3eval (monomial n c) x = (c : ℝ)*x^n := by
  induction n with
  | zero => simp [monomial,s3eval]
  | succ n ih =>
    simp [monomial,List.replicate_succ,s3eval] at ih ⊢
    rw [ih]
    ring

open scoped BigOperators

theorem eval_sumRange (f : ℕ → List ℚ) (n : ℕ) (x : ℝ) :
    s3eval (sumRange f n) x = ∑ k ∈ Finset.range n, s3eval (f k) x := by
  induction n with
  | zero => simp [sumRange,s3eval]
  | succ n ih => rw [sumRange,eval_add,ih,Finset.sum_range_succ]

/-- Coefficients of the integrated odd-logarithm/geometric product. -/
def innerCoeffs (n m : ℕ) : List ℚ :=
  scale 2 (sumRange (fun i => sumRange (fun j =>
    monomial (2*i+j+2) (1/((2*i+1 : ℕ)*(2*i+j+2 : ℕ) : ℚ))) m) n)

theorem eval_innerCoeffs (n m : ℕ) (x : ℝ) :
    s3eval (innerCoeffs n m) x = goldbachS3_innerPolynomial n m x := by
  simp [innerCoeffs,eval_scale,eval_sumRange,eval_monomial,
    goldbachS3_innerPolynomial,div_eq_mul_inv,mul_comm]

/-- A geometric polynomial with exact rational coefficients. -/
def geom (c : ℚ) (n : ℕ) : List ℚ := sumRange (fun k => monomial k (c^k)) n

theorem eval_geom (c : ℚ) (n : ℕ) (x : ℝ) :
    s3eval (geom c n) x = ∑ k ∈ Finset.range n, ((c : ℝ)*x)^k := by
  simp [geom,eval_sumRange,eval_monomial,mul_pow]

/-- Coefficients of the shifted inner polynomial times the geometric kernel majorant. -/
def segmentCoeffs (cs : List ℚ) (a : ℚ) : List ℚ :=
  mul (add (translate a cs) [a/10^9,1/10^9])
    (add (scale (-8/(3-a)) (geom (1/(3-a)) 64))
      (scale (360/(29-45*a)) (add (geom (45/(29-45*a)) 64) [(5/2)*(3/5)^64])))

theorem eval_segmentCoeffs (cs : List ℚ) (a : ℚ) (y : ℝ) :
    s3eval (segmentCoeffs cs a) y =
      (s3eval cs ((a : ℝ)+y) + ((a : ℝ)+y)/10^9) *
        (-8/(3-(a : ℝ))*(∑ k ∈ Finset.range 64, (y/(3-(a : ℝ)))^k) +
          360/(29-45*(a : ℝ))*((∑ k ∈ Finset.range 64, (45*y/(29-45*(a : ℝ)))^k) +
            (5/2 : ℝ)*(3/5)^64)) := by
  simp only [segmentCoeffs,eval_mul,eval_add,eval_translate,eval_scale,eval_geom,s3eval,
    Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_neg,
    mul_zero,add_zero]
  congr 1
  · ring
  · congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      ring
    · congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      ring

end S3Polynomial
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

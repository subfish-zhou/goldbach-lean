import WR2IntegerLogHorner
import WR2ClassicalFifthPolynomialData

/-! Exact paired natural-number evaluation of the original polynomial.
Exact regrouping only: the coefficients, domain and payment precision are unchanged. -/
namespace WuPaper.FifthIntegerPolynomial

/-- This hypothesis, not an assumption about Nat subtraction, justifies every pair. -/
theorem pair_no_truncation {Y D a b : ℕ} (hYD : Y ≤ D) (hba : b ≤ a) :
    b*Y ≤ a*D := Nat.mul_le_mul hba hYD

def commonDen : ℕ := 52254720

def homogeneous (Y D : ℕ) : ℕ :=
  Y^3*((1451520*D-1088640*Y)*D^8+
    Y^2*((653184*D-374976*Y)*D^6+
      Y^2*((155616*D-57108*Y)*D^4+
        Y^2*((18212*D-4030*Y)*D^2+
          Y^2*(780*D-105*Y)))))

def rationalHomogeneous (Y D : ℚ) : ℚ :=
  Y^3*((1451520*D-1088640*Y)*D^8+
    Y^2*((653184*D-374976*Y)*D^6+
      Y^2*((155616*D-57108*Y)*D^4+
        Y^2*((18212*D-4030*Y)*D^2+
          Y^2*(780*D-105*Y)))))

/-- All five subtractions are exact before any cast is distributed. -/
theorem cast_homogeneous {Y D : ℕ} (hYD : Y ≤ D) :
    (homogeneous Y D : ℚ) = rationalHomogeneous (Y:ℚ) (D:ℚ) := by
  have h0 : 1088640*Y ≤ 1451520*D := pair_no_truncation hYD (by decide)
  have h1 : 374976*Y ≤ 653184*D := pair_no_truncation hYD (by decide)
  have h2 : 57108*Y ≤ 155616*D := pair_no_truncation hYD (by decide)
  have h3 : 4030*Y ≤ 18212*D := pair_no_truncation hYD (by decide)
  have h4 : 105*Y ≤ 780*D := pair_no_truncation hYD (by decide)
  simp only [homogeneous,rationalHomogeneous,Nat.cast_mul,Nat.cast_add,
    Nat.cast_pow,Nat.cast_sub h0,Nat.cast_sub h1,Nat.cast_sub h2,
    Nat.cast_sub h3,Nat.cast_sub h4,Nat.cast_ofNat]

/-- Prove this at abstract Y,D; do not expand a concrete grid denominator. -/
theorem cPoly_abstract (Y D : ℚ) (hD : D ≠ 0) :
    ClassicalFifthTableCheck.cPoly (Y/D) =
      rationalHomogeneous Y D / ((commonDen:ℚ)*D^12) := by
  norm_num [ClassicalFifthTableCheck.cPoly,rationalHomogeneous,commonDen]
  field_simp [hD]
  ring

/-- Exact cPoly evaluation by Nat arithmetic on its original nonnegative domain. -/
theorem cPoly_nat {Y D : ℕ} (hYD : Y ≤ D) (hD : 0 < D) :
    (homogeneous Y D:ℚ)/((commonDen:ℚ)*(D:ℚ)^12) =
      ClassicalFifthTableCheck.cPoly ((Y:ℚ)/(D:ℚ)) := by
  have hd : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [cast_homogeneous hYD]
  exact (cPoly_abstract (Y:ℚ) (D:ℚ) hd).symm

end WuPaper.FifthIntegerPolynomial
#print axioms WuPaper.FifthIntegerPolynomial.cPoly_nat

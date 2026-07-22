import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-!
# Three-dimensional Jacobian counterexample audit

This file records the polynomial map and exact rational witness points from the
public claim pinned in `SOURCE.md`. It checks only the displayed algebraic
identities; it does not establish source priority or statement fidelity.
-/

namespace ProofweaveJacobian

open MvPolynomial

noncomputable section

abbrev P := MvPolynomial (Fin 3) ℚ

def x : P := X 0
def y : P := X 1
def z : P := X 2

def f₁ : P :=
  (1 + x * y) ^ 3 * z + y ^ 2 * (1 + x * y) * (4 + 3 * x * y)

def f₂ : P :=
  y + 3 * x * (1 + x * y) ^ 2 * z + 3 * x * y ^ 2 * (4 + 3 * x * y)

def f₃ : P :=
  2 * x - 3 * x ^ 2 * y - x ^ 3 * z

def jacobianDet : P :=
  pderiv 0 f₁ * (pderiv 1 f₂ * pderiv 2 f₃ - pderiv 2 f₂ * pderiv 1 f₃) -
  pderiv 1 f₁ * (pderiv 0 f₂ * pderiv 2 f₃ - pderiv 2 f₂ * pderiv 0 f₃) +
  pderiv 2 f₁ * (pderiv 0 f₂ * pderiv 1 f₃ - pderiv 1 f₂ * pderiv 0 f₃)

@[simp]
theorem pderiv_two (i : Fin 3) : pderiv i (2 : P) = 0 := by
  change pderiv i (C (2 : ℚ)) = 0
  exact pderiv_C

@[simp]
theorem pderiv_three (i : Fin 3) : pderiv i (3 : P) = 0 := by
  change pderiv i (C (3 : ℚ)) = 0
  exact pderiv_C

@[simp]
theorem pderiv_four (i : Fin 3) : pderiv i (4 : P) = 0 := by
  change pderiv i (C (4 : ℚ)) = 0
  exact pderiv_C

structure Point3 where
  x : ℚ
  y : ℚ
  z : ℚ
deriving DecidableEq

@[ext]
theorem Point3.ext {left right : Point3}
    (x_eq : left.x = right.x)
    (y_eq : left.y = right.y)
    (z_eq : left.z = right.z) : left = right := by
  cases left
  cases right
  simp_all

def Point3.coordinate (point : Point3) : Fin 3 → ℚ
  | 0 => point.x
  | 1 => point.y
  | 2 => point.z

def polynomialMap (point : Point3) : Point3 := {
  x := eval point.coordinate f₁
  y := eval point.coordinate f₂
  z := eval point.coordinate f₃
}

def point₀ : Point3 := ⟨0, 0, -1 / 4⟩
def point₁ : Point3 := ⟨1, -3 / 2, 13 / 2⟩
def point₂ : Point3 := ⟨-1, 3 / 2, 13 / 2⟩
def commonImage : Point3 := ⟨-1 / 4, 0, 0⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem jacobianDet_eq_neg_two : jacobianDet = (-2 : P) := by
  simp [jacobianDet, f₁, f₂, f₃, x, y, z]
  ring

theorem point₀_ne_point₁ : point₀ ≠ point₁ := by
  intro equality
  have firstCoordinate := congrArg Point3.x equality
  norm_num [point₀, point₁] at firstCoordinate

theorem point₀_ne_point₂ : point₀ ≠ point₂ := by
  intro equality
  have firstCoordinate := congrArg Point3.x equality
  norm_num [point₀, point₂] at firstCoordinate

theorem point₁_ne_point₂ : point₁ ≠ point₂ := by
  intro equality
  have firstCoordinate := congrArg Point3.x equality
  norm_num [point₁, point₂] at firstCoordinate

theorem polynomialMap_point₀ : polynomialMap point₀ = commonImage := by
  apply Point3.ext <;>
    norm_num [polynomialMap, Point3.coordinate, point₀, commonImage, f₁, f₂, f₃, x, y, z]

theorem polynomialMap_point₁ : polynomialMap point₁ = commonImage := by
  apply Point3.ext <;>
    norm_num [polynomialMap, Point3.coordinate, point₁, commonImage, f₁, f₂, f₃, x, y, z]

theorem polynomialMap_point₂ : polynomialMap point₂ = commonImage := by
  apply Point3.ext <;>
    norm_num [polynomialMap, Point3.coordinate, point₂, commonImage, f₁, f₂, f₃, x, y, z]

theorem polynomialMap_not_injective : ¬ Function.Injective polynomialMap := by
  intro injective
  apply point₀_ne_point₁
  apply injective
  exact polynomialMap_point₀.trans polynomialMap_point₁.symm

theorem jacobian_counterexample_audit :
    jacobianDet = (-2 : P) ∧
    point₀ ≠ point₁ ∧ point₀ ≠ point₂ ∧ point₁ ≠ point₂ ∧
    polynomialMap point₀ = commonImage ∧
    polynomialMap point₁ = commonImage ∧
    polynomialMap point₂ = commonImage ∧
    ¬ Function.Injective polynomialMap := by
  exact ⟨
    jacobianDet_eq_neg_two,
    point₀_ne_point₁,
    point₀_ne_point₂,
    point₁_ne_point₂,
    polynomialMap_point₀,
    polynomialMap_point₁,
    polynomialMap_point₂,
    polynomialMap_not_injective
  ⟩

end

end ProofweaveJacobian

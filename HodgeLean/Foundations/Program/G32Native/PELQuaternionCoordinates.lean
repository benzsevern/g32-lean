import HodgeLean.Foundations.Program.G32Native.PELQuaternionPresentation
import Mathlib.Algebra.Star.Module

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The universal quaternion map is the coordinate map of the retained basis.
Source: Voight, Quaternion Algebras, §2.2 (the basis 1, i, j, ij). -/
theorem quaternion_coordinates_formula {D : Type*} [Ring D] [Algebra ℚ D]
    {b : ℚ} (q : QuaternionAlgebra.Basis D (-3 : ℚ) 0 b)
    (e : Module.Basis (Fin 4) ℚ D)
    (h0 : e 0 = 1) (h1 : e 1 = q.i) (h2 : e 2 = q.j) (h3 : e 3 = q.k)
    (x : ℍ[ℚ, -3, 0, b]) :
    q.liftHom x = e.equivFun.symm (QuaternionAlgebra.linearEquivTuple (-3 : ℚ) 0 b x) := by
  change algebraMap ℚ D x.re + x.imI • q.i + x.imJ • q.j + x.imK • q.k =
    e.equivFun.symm ![x.re, x.imI, x.imJ, x.imK]
  rw [Module.Basis.equivFun_symm_apply]
  simp [Fin.sum_univ_succ, h0, h1, h2, h3, Algebra.algebraMap_eq_smul_one,
    add_assoc]


/-- Construct the presentation from four explicit basis values.
Source: Voight, Quaternion Algebras, §2.2. -/
def quaternionPresentationOfBasis {D : Type*} [Ring D] [Algebra ℚ D]
    {b : ℚ} (q : QuaternionAlgebra.Basis D (-3 : ℚ) 0 b)
    (e : Module.Basis (Fin 4) ℚ D)
    (h0 : e 0 = 1) (h1 : e 1 = q.i) (h2 : e 2 = q.j) (h3 : e 3 = q.k) :
    ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] D :=
  quaternionPresentation q e (quaternion_coordinates_formula q e h0 h1 h2 h3)

/-- Quaternion conjugation agrees with the retained involution when it negates
all three pure basis vectors.
Source: Voight, Quaternion Algebras, §3.2 (standard involution). -/
theorem quaternion_lift_star {D : Type*} [Ring D] [Algebra ℚ D]
    [StarRing D] [StarModule ℚ D]
    {b : ℚ} (q : QuaternionAlgebra.Basis D (-3 : ℚ) 0 b)
    (hi : star q.i = -q.i) (hj : star q.j = -q.j) (hk : star q.k = -q.k)
    (x : ℍ[ℚ, -3, 0, b]) : q.liftHom (star x) = star (q.liftHom x) := by
  simp [QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift,
    hi, hj, hk, Algebra.algebraMap_eq_smul_one]

/-- A positive scalar norm of the second pure basis vector forces b < 0.
The equality ties the sign test to multiplication and the retained involution.
Source: Voight, Quaternion Algebras, §14.5 (definiteness at the real place). -/
theorem quaternion_negative_parameter {D : Type*} [Ring D] [Algebra ℚ D]
    [Nontrivial D] [Star D] {b : ℚ}
    (q : QuaternionAlgebra.Basis D (-3 : ℚ) 0 b)
    (hj : star q.j = -q.j) (t : ℚ) (ht : 0 < t)
    (hn : q.j * star q.j = algebraMap ℚ D t) : b < 0 := by
  have h : algebraMap ℚ D (-b) = algebraMap ℚ D t := by
    rw [hj, mul_neg, q.j_mul_j] at hn
    simpa only [map_neg, Algebra.algebraMap_eq_smul_one] using hn
  have he := (algebraMap ℚ D).injective h
  linarith

#print axioms quaternion_coordinates_formula
#print axioms quaternionPresentationOfBasis
#print axioms quaternion_lift_star
#print axioms quaternion_negative_parameter
end HodgeLean.Foundations.Program.GeneralTypeIII

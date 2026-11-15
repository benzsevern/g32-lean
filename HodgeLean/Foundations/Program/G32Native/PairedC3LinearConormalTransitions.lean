import HodgeLean.Foundations.Program.SchoenCycleS3CotangentBasis
import Mathlib.LinearAlgebra.Basis.SMul

/-! # Denominator changes for affine linear conormal generators -/

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program MvPolynomial

/-- A change of denominator acts on the actual ideal class, including
when its representative has an additional quadratic term. -/
theorem paired_c3_conormal_class_change {A : Type*} [CommRing A]
    (I : Ideal A) (f g : I) (u : A)
    (h : (g : A) - u * (f : A) ∈ I ^ 2) :
    I.toCotangent g = u • I.toCotangent f := by
  rw [← map_smul]
  exact I.toCotangent_eq.mpr h

/-- The same denominator-change formula holds under the actual map
on ideal quotients induced by an overlap ring homomorphism. -/
theorem paired_c3_conormal_overlap_map {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (I : Ideal A) (J : Ideal B) (f : A →ₐ[R] B) (h : I ≤ J.comap f)
    (x : I) (y : J) (u : B) (hxy : f (x : A) - u * (y : B) ∈ J ^ 2) :
    Ideal.mapCotangent I J f h (I.toCotangent x) = u • J.toCotangent y := by
  rw [Ideal.mapCotangent_toCotangent]
  exact paired_c3_conormal_class_change J y _ u hxy

/-- Scaling the affine linear equations by a unit scales the conormal
basis by that same unit, rather than its inverse. -/
def pairedC3ScaledCoordinateConormalBasis {A σ τ : Type*} [CommRing A]
    (e : τ ↪ σ)
    (u : (MvPolynomial σ A ⧸
      Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ A))))ˣ) :
    let I := Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ A)))
    Module.Basis τ (MvPolynomial σ A ⧸ I) I.Cotangent :=
  (s2e_coordinateCotangentBasis (R := A) e).unitsSMul (fun _ => u)

/-- The rescaled basis uses the original coordinate ideal classes. -/
theorem paired_c3_scaled_coordinate_conormal_basis_apply
    {A σ τ : Type*} [CommRing A] (e : τ ↪ σ)
    (u : (MvPolynomial σ A ⧸
      Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ A))))ˣ)
    (j : τ) :
    pairedC3ScaledCoordinateConormalBasis e u j =
      u • (Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ A)))).toCotangent
        ⟨X (e j), Ideal.subset_span ⟨j, rfl⟩⟩ := by
  rw [pairedC3ScaledCoordinateConormalBasis, Module.Basis.unitsSMul_apply,
    s2e_coordinateCotangentBasis_apply]

/-- Coordinates of a section transform by the inverse unit. This
distinguishes a change of frame from a change of coefficients. -/
theorem paired_c3_scaled_coordinate_conormal_repr
    {A σ τ : Type*} [CommRing A] (e : τ ↪ σ)
    (u : (MvPolynomial σ A ⧸
      Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ A))))ˣ)
    (v : (Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ A)))).Cotangent)
    (j : τ) :
    (pairedC3ScaledCoordinateConormalBasis e u).repr v j =
      u⁻¹ • (s2e_coordinateCotangentBasis (R := A) e).repr v j :=
  Module.Basis.repr_unitsSMul _ _ _ _

end HodgeLean.Foundations.Program.G32Native

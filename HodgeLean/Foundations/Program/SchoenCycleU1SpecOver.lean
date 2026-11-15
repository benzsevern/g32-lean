import Mathlib.Basic.Complex.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Affine schemes over the complex base -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The affine complex scheme with its specified algebra structure.
Source: Hartshorne, Algebraic Geometry, II.2, affine schemes over a base. -/
def s2e_u1_specOver (A : Type) [CommRing A] [Algebra ℂ A] : Over (Spec ↧ℂ) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

/-- The affine morphism over the complex base induced by an algebra map.
Source: Mathlib, `Spec.homEquivAlgHom`; Hartshorne, Algebraic Geometry, II.2. -/
def s2e_u1_specOverMap {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (u : A →ₐ[ℂ] B) :
    s2e_u1_specOver B ⟶ s2e_u1_specOver A :=
  Over.homMk (Spec.map (CommRingCat.ofHom u.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom u.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ B))
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext u.comp_algebraMap)

end HodgeLean.Foundations.Program

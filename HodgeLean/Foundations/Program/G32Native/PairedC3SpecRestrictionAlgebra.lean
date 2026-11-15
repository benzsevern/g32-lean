import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveRestriction

/-! # Complex coefficients retained from the original affine structure maps -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The algebra on an original affine coordinate ring induced by its
specified structure morphism to the complex base. -/
def pairedC3SpecAlgebra {B : Type} [CommRing B]
    (p : Spec (CommRingCat.of B) ⟶ Spec ↧ℂ) : Algebra ℂ B :=
  (Spec.preimage p).hom.toAlgebra

/-- This choice retains the original structure map exactly. -/
theorem pairedC3_spec_algebra_structure_map {B : Type} [CommRing B]
    (p : Spec (CommRingCat.of B) ⟶ Spec ↧ℂ) :
    letI := pairedC3SpecAlgebra p
    ComplexPoint.affineSpecStructureMap B = p := by
  letI := pairedC3SpecAlgebra p
  exact Spec.map_preimage p

/-- A restriction over the original complex base is an algebra map for
the induced coefficient structures, with its original ring map retained. -/
def pairedC3SpecRestrictionAlgHom {A B : Type} [CommRing A] [CommRing B]
    (pA : Spec (CommRingCat.of A) ⟶ Spec ↧ℂ)
    (pB : Spec (CommRingCat.of B) ⟶ Spec ↧ℂ) (r : A →+* B)
    (h : Spec.map (CommRingCat.ofHom r) ≫ pA = pB) :
    letI := pairedC3SpecAlgebra pA
    letI := pairedC3SpecAlgebra pB
    A →ₐ[ℂ] B := by
  letI := pairedC3SpecAlgebra pA
  letI := pairedC3SpecAlgebra pB
  refine ⟨r, ?_⟩
  have hc : CommRingCat.ofHom (algebraMap ℂ A) ≫ CommRingCat.ofHom r =
      CommRingCat.ofHom (algebraMap ℂ B) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change Spec.map (CommRingCat.ofHom r) ≫
      ComplexPoint.affineSpecStructureMap A = ComplexPoint.affineSpecStructureMap B
    rw [pairedC3_spec_algebra_structure_map pA, pairedC3_spec_algebra_structure_map pB]
    exact h
  intro z
  exact congrArg (fun F => F.hom z) hc

#print axioms pairedC3SpecAlgebra
#print axioms pairedC3_spec_algebra_structure_map
#print axioms pairedC3SpecRestrictionAlgHom
end HodgeLean.Foundations.Program.G32Native

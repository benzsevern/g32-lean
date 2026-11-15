import HodgeLean.Foundations.TubularEuler.ActualConormalSectionDataHelpers
import HodgeLean.Foundations.BundleThom.ConormalFibre

/-! # The original fibre value of a descended regular equation

The section value is explicitly typed in the original conormal fibre before
applying any affine tensor comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

/-- The value of the original conormal section descended from a regular ideal
equation, retained in the original scheme fibre.
Source: Hartshorne, Algebraic Geometry, II.8, conormal sheaf and its fibres.
For example, the affine cotangent comparison evaluates this value on the
pure tensor of the same original regular equation.
HC no distance; AV milestone no distance. -/
opaque originalRegularConormalValueData
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) :
    {w : BundleThom.i1_conormalFibre j x //
      w = BundleResolution.i1_moduleSectionValue (Conormal.sheaf j) (j ⁻¹ᵁ A)
        (actualConormalAffineSectionData j A hA u).localSection x hx} :=
  ⟨BundleResolution.i1_moduleSectionValue (Conormal.sheaf j) (j ⁻¹ᵁ A)
    (actualConormalAffineSectionData j A hA u).localSection x hx, rfl⟩

/-- Retain the constructed original fibre value behind its evaluation equation.
Source: `originalRegularConormalValueData`; Hartshorne, Algebraic Geometry, II.8.
For example, `originalRegularConormalValue_eq` recovers its original section value. -/
def originalRegularConormalValue
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) :
    BundleThom.i1_conormalFibre j x :=
  (originalRegularConormalValueData j A hA u x hx).val

#print axioms originalRegularConormalValueData
#print axioms originalRegularConormalValue

/-- The stored original conormal value is the value of the specified descended
section, before applying any affine comparison.
Source: definition of `originalRegularConormalValue`.
HC no distance; AV milestone no distance. -/
theorem originalRegularConormalValue_eq
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) :
    originalRegularConormalValue j A hA u x hx =
      BundleResolution.i1_moduleSectionValue (Conormal.sheaf j) (j ⁻¹ᵁ A)
        (actualConormalAffineSectionData j A hA u).localSection x hx :=
  (originalRegularConormalValueData j A hA u x hx).property

#print axioms originalRegularConormalValue_eq

end HodgeLean.Foundations.TubularEuler

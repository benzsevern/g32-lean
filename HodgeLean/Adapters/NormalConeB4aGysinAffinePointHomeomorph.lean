import HodgeLean.Adapters.NormalConeB4aGysinAffineEvaluation
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- The affine spectrum chart respects the original complex structure map. -/
theorem a3b4a_gysin_affine_fromSpec_over
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of ℂ))
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra ℂ Γ(X, U) := overSpecAlgebra (Over.mk q) U
    hU.fromSpec ≫ q = ComplexPoint.affineSpecStructureMap Γ(X, U) := by
  letI : Algebra ℂ Γ(X, U) := overSpecAlgebra (Over.mk q) U
  change hU.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (a3b4a_gysin_sectionConst q U))
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- Complex points over an affine open are homeomorphic to complex
algebra evaluations on its section ring. -/
def a3b4a_gysin_affine_point_homeomorph
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of ℂ))
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra ℂ Γ(X, U) := overSpecAlgebra (Over.mk q) U
    {w : ComplexPoint (Over.mk q) // w.underlying ∈ U} ≃ₜ (Γ(X, U) →ₐ[ℂ] ℂ) := by
  letI : Algebra ℂ Γ(X, U) := overSpecAlgebra (Over.mk q) U
  have he : hU.isoSpec.hom ≫ ComplexPoint.affineSpecStructureMap Γ(X, U) = U.ι ≫ q := by
    apply (cancel_epi hU.isoSpec.inv).mp
    rw [Iso.inv_hom_id_assoc, ← Category.assoc, hU.isoSpec_inv_ι,
      a3b4a_gysin_affine_fromSpec_over q U hU]
  let ei : ComplexPoint.openScheme (Over.mk q) U ≅
      Over.mk (ComplexPoint.affineSpecStructureMap Γ(X, U)) := Over.isoMk hU.isoSpec he
  let e := Point.isoMapHomeomorph ei
  exact (ComplexPoint.openHomeomorph (Over.mk q) U).symm.trans
    (e.trans (ComplexPoint.affineSpecHomeomorph Γ(X, U)))

end HodgeLean.Adapters

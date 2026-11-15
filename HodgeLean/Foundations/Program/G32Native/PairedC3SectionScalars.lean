import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf

/-! # Local scalar coordinates with the original structural base action -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- A local-ring-linear scalar coordinate is linear for the original
structural action of the coefficient ring. -/
def pairedC3SectionScalarEquivOverBase {R : Type} [CommRing R] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of R)) {M : X.Modules} {U : X.Opens}
    (e : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U)) :
    sectionModuleOverBase f M U ≃ₗ[R] (OModulePresheaf.unit f).obj U where
  toFun x := e (show Γ(M, U) from x)
  invFun a := e.symm (show Γ(X, U) from a)
  left_inv x := e.symm_apply_apply x
  right_inv a := e.apply_symm_apply a
  map_add' x y := e.map_add x y
  map_smul' r x := by
    change e ((f.constToPresheaf.app (op U)).hom r • (show Γ(M, U) from x)) =
      (f.constToPresheaf.app (op U)).hom r * e (show Γ(M, U) from x)
    exact e.map_smul ((f.constToPresheaf.app (op U)).hom r) x

#print axioms pairedC3SectionScalarEquivOverBase
end HodgeLean.Foundations.Program.G32Native

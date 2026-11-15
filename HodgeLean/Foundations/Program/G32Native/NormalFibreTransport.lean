import HodgeLean.Foundations.Program.G32Native.CanonicalNormalGluing
import Mathlib.LinearAlgebra.Dual.Defs

/-! # Dual fibres of the retained conormal comparison -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- Pull a module sheaf to the specified complex point and take its complex dual.
Source: Hartshorne, Algebraic Geometry, II.8, normal-conormal duality. -/
abbrev normalFibreOfModule {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules)
    (x : ComplexPoint Q) :=
  Module.Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
    ((Scheme.Modules.pullback x.left).obj M))

/-- Transport the actual dual conormal fibre, with its original point retained.
Source: Hartshorne, Algebraic Geometry, II.8, normal-conormal duality. -/
def normalFibreTransport {Q : Over (Spec ↧ℂ)} {M N : Q.left.Modules}
    (E : M ≅ N) (x : ComplexPoint Q) :
    normalFibreOfModule M x ≃ₗ[ℂ] normalFibreOfModule N x :=
  (((Scheme.Modules.pullback x.left ⋙ moduleSpecΓFunctor).mapIso E).toLinearEquiv).symm.dualMap

/-- The transported normal vector evaluates on the original inverse conormal map.
Source: Hartshorne, Algebraic Geometry, II.8, duality of conormal maps. -/
theorem normalFibreTransport_apply {Q : Over (Spec ↧ℂ)} {M N : Q.left.Modules}
    (E : M ≅ N) (x : ComplexPoint Q) (v : normalFibreOfModule M x)
    (w : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x.left).obj N)) :
    normalFibreTransport E x v w =
      v (((Scheme.Modules.pullback x.left ⋙ moduleSpecΓFunctor).map E.inv) w) := rfl

/-- Composition of actual conormal identifications transports normal fibres in order.
Source: Hartshorne, Algebraic Geometry, II.8, functoriality of normal-conormal duality. -/
theorem normalFibreTransport_trans {Q : Over (Spec ↧ℂ)} {M N L : Q.left.Modules}
    (E : M ≅ N) (F : N ≅ L) (x : ComplexPoint Q) :
    normalFibreTransport (E ≪≫ F) x =
      (normalFibreTransport E x).trans (normalFibreTransport F x) := by
  ext v w
  change v (((Scheme.Modules.pullback x.left ⋙ moduleSpecΓFunctor).map (F.inv ≫ E.inv)) w) = _
  rw [Functor.map_comp]
  rfl

#print axioms normalFibreOfModule
#print axioms normalFibreTransport
#print axioms normalFibreTransport_apply
#print axioms normalFibreTransport_trans
end HodgeLean.Foundations.Program.G32Native

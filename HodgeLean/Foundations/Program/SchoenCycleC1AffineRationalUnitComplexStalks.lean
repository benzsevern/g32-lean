import HodgeLean.Foundations.Program.SchoenCycleC1AffineRationalUnitMaximalStalks
import HodgeLean.Foundations.Program.SchoenCycleC1FiniteFibreComplexPoints

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Rational unit representatives at the actual complex points suffice to
construct a unit on the entire original finite-type affine chart. -/
theorem s2e_c1_affine_rational_unit_of_complex_stalks
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (t : X.left.functionField) (ht : t ≠ 0)
    (hlocal : ∀ x : ComplexPoint X, x.underlying ∈ U →
      ∃ u : (X.left.presheaf.stalk x.underlying)ˣ,
        algebraMap (X.left.presheaf.stalk x.underlying) X.left.functionField (u : _) = t) :
    ∃ u : Γ(X.left, U)ˣ, X.left.germToFunctionField U (u : Γ(X.left, U)) = t := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hclosed (p : X.left) (hp : p ∈ U) (hc : IsClosed ({p} : Set X.left)) :
      ∃ u : (X.left.presheaf.stalk p)ˣ,
        algebraMap (X.left.presheaf.stalk p) X.left.functionField (u : _) = t := by
    let x : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom p hc)
      (pointOfClosedPoint_comp X.hom p hc)
    have hx : x.underlying = p := pointOfClosedPoint_apply X.hom p hc _
    have h := hlocal x (by rw [hx]; exact hp)
    exact (congrArg (fun q : X.left => ∃ u : (X.left.presheaf.stalk q)ˣ,
      algebraMap (X.left.presheaf.stalk q) X.left.functionField (u : _) = t) hx) ▸ h
  apply s2e_c1_affine_rational_unit_of_maximal_stalks X.left U hU t ht
  intro P hP
  have hp : hU.fromSpec P ∈ U := by
    change P ∈ hU.fromSpec ⁻¹ᵁ U
    rw [hU.fromSpec_preimage_self]
    trivial
  exact hclosed _ hp (hU.fromSpec.closedPoints_subset_preimage_closedPoints
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mpr hP))

end HodgeLean.Foundations.Program

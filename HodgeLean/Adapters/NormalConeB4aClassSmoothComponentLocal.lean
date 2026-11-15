import HodgeLean.Adapters.NormalConeB4aClassComponentLocalDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalCoordinates

/-! # Smooth component dimension from a local ambient chart

Route: a nonempty open of the integral reduced component is integral and
smooth. Its relative dimension is constant. Compare coheights at the given
closed point with the nonprojective component dimension formula.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- A component's smooth locus has relative dimension `d-c`, detected at any
closed point on that locus using one standard-smooth ambient affine chart. -/
theorem a3b4a_classComponent_smoothLocus_relativeDimension_local
    (X : Over (Spec (CommRingCat.of ℂ))) {d c : ℕ}
    [Smooth X.hom]
    (x : X.left) (hx : Order.coheight x = c) (z : cycleComponent X.left x)
    (hz : z ∈ (cycleComponentι X.left x ≫ X.hom).smoothLocus) (hzClosed : IsClosed {z})
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hyU : cycleComponentι X.left x z ∈ U)
    (hs : (X.hom.appLE ⊤ U (by simp)).hom.IsStandardSmoothOfRelativeDimension d) :
    SmoothOfRelativeDimension (d - c)
      ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫ cycleComponentι X.left x ≫ X.hom) := by
  let A := (cycleComponentι X.left x ≫ X.hom).smoothLocus
  let g := A.ι ≫ cycleComponentι X.left x ≫ X.hom
  letI : Nonempty A.toScheme := ⟨⟨z, hz⟩⟩
  letI : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
  letI : Smooth g := (cycleComponentι X.left x ≫ X.hom).smooth_restrict_smoothLocus
  obtain ⟨m, hm⟩ := Smooth.exists_smoothOfRelativeDimension g
  let zA : A.toScheme := ⟨z, hz⟩
  have hzAClosed : IsClosed ({zA} : Set A) := by
    have he : A.ι ⁻¹' ({z} : Set (cycleComponent X.left x)) = {zA} := by
      ext a
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    exact he ▸ hzClosed.preimage A.ι.continuous
  have hmEq : m = d - c := by
    exact_mod_cast calc
      (m : ℕ∞) = Order.coheight zA :=
        (SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
          (f := g) (d := m) zA hzAClosed).symm
      _ = Order.coheight z := (coheight_eq_of_isOpenImmersion (x := zA) A.ι).symm
      _ = d - c := a3b4a_classComponent_closedPoint_coheight_local X x z hx hzClosed U hU hyU hs
  subst m
  exact hm

end HodgeLean.Adapters

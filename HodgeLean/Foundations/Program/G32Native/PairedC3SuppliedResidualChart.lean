import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualChartCoordinates
import HodgeLean.Adapters.IntersectionProductScaf

/-! # Residual quotient coordinates on an actual supplied affine chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Adapters

/-- A coefficient-preserving binomial chart of a supplied morphism identifies
its actual residual quotient with the affine line over the actual base quotient.
The original ratio is retained.
Source: Hartshorne, Algebraic Geometry, II.7.13; Fulton B.6. -/
theorem pairedC3_supplied_residual_chart
    {X Y : Scheme} (p : Y ⟶ X) (M : X.IdealSheafData)
    (U : X.affineOpens) (V : Y.affineOpens) (hV : V.1 ≤ p ⁻¹ᵁ U.1)
    (u v : Γ(X, U)) (hu : u ∈ M.ideal U) (hv : v ∈ M.ideal U)
    (e : ring u v ≃+* Γ(Y, V))
    (he : e.toRingHom.comp (coeff u v) = (p.appLE U.1 V.1 hV).hom) :
    ∃ E : (Γ(Y, V) ⧸ (M.comap p).ideal V) ≃+* (Γ(X, U) ⧸ M.ideal U)[X],
      (∀ z : ring u v,
        E (Ideal.Quotient.mk ((M.comap p).ideal V) (e z)) =
          pairedC3ResidualChartEquiv u v (M.ideal U) hu hv
            (Ideal.Quotient.mk ((M.ideal U).map (coeff u v)) z)) ∧
      E (Ideal.Quotient.mk ((M.comap p).ideal V) (e (ratio u v))) = Polynomial.X := by
  have hM : (M.comap p).ideal V =
      ((M.ideal U).map (coeff u v)).map e.toRingHom := by
    rw [IntersectionProductScaf_comap_ideal_affine_charts p M U V hV,
      Ideal.map_map, he]
  let q := Ideal.quotientEquiv ((M.ideal U).map (coeff u v))
    ((M.comap p).ideal V) e hM
  let a := pairedC3ResidualChartEquiv u v (M.ideal U) hu hv
  let E := q.symm.trans a
  have hz (z : ring u v) :
      E (Ideal.Quotient.mk ((M.comap p).ideal V) (e z)) =
        a (Ideal.Quotient.mk ((M.ideal U).map (coeff u v)) z) := by
    change a (q.symm (q (Ideal.Quotient.mk ((M.ideal U).map (coeff u v)) z))) = _
    rw [RingEquiv.symm_apply_apply]
  refine ⟨E, hz, ?_⟩
  exact (hz (ratio u v)).trans (pairedC3_residual_chart_ratio u v (M.ideal U) hu hv)

#print axioms pairedC3_supplied_residual_chart
end HodgeLean.Foundations.Program.G32Native

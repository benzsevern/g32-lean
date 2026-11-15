import HodgeLean.Foundations.Program.SchoenCycleC1PowerGenericFieldMaps
import HodgeLean.Foundations.Program.SchoenCycleC1CurveRationalOrderData
import HodgeLean.Foundations.Program.SchoenCycleSmoothPowerJets

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual coordinate rational product retains its original curve
unit factorizations and the same point-indexed orders in every tuple stalk. -/
theorem s2e_c1_power_rational_product_order_data
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left]
    [Smooth Y.hom] [SmoothOfRelativeDimension 1 Y.hom] [IsProjective Y.hom]
    (N : ℕ) (f : Y.left.functionField) (hf : f ≠ 0) :
    ∃ φ : Fin N → (Y.left.functionField →+* (g3_power Y N).left.functionField),
      (∀ i, Function.Injective (φ i) ∧
        ∀ (p : (g3_power Y N).left) (r : Y.left.presheaf.stalk ((g3_proj Y N i).left p)),
          φ i (algebraMap (Y.left.presheaf.stalk ((g3_proj Y N i).left p)) Y.left.functionField r) =
            algebraMap ((g3_power Y N).left.presheaf.stalk p) (g3_power Y N).left.functionField
              (((g3_proj Y N i).left.stalkMap p).hom r)) ∧ (∏ i, φ i f) ≠ 0 ∧
      ∃ n : ComplexPoint Y → ℤ,
        (∃ u : ∀ p : ComplexPoint Y, (Y.left.presheaf.stalk p.underlying)ˣ,
          ∀ p, f = algebraMap (Y.left.presheaf.stalk p.underlying) Y.left.functionField (u p : _) *
            algebraMap (Y.left.presheaf.stalk p.underlying) Y.left.functionField
              (s2e_native_curve_parameter Y p) ^ n p) ∧
        ∀ x : ComplexPoint (g3_power Y N),
        ∃ u : ((g3_power Y N).left.presheaf.stalk x.underlying)ˣ,
          (∏ i, φ i f) =
            algebraMap ((g3_power Y N).left.presheaf.stalk x.underlying)
              (g3_power Y N).left.functionField (u : _) *
            ∏ i, (algebraMap ((g3_power Y N).left.presheaf.stalk x.underlying)
              (g3_power Y N).left.functionField (s2e_curvePowerParameter Y N x i)) ^
                n (Point.map (g3_proj Y N i) x) := by
  obtain ⟨φ, hφ⟩ := s2e_c1_power_generic_field_maps Y N
  obtain ⟨n, u, hu⟩ := s2e_c1_curve_rational_order_data Y f hf
  refine ⟨φ, hφ, ?_, n, ⟨u, hu⟩, ?_⟩
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact fun h => hf ((hφ i).1 (h.trans (map_zero _).symm))
  · intro x
    let p (i : Fin N) := Point.map (g3_proj Y N i) x
    let R := (g3_power Y N).left.presheaf.stalk x.underlying
    let v (i : Fin N) : Rˣ := Units.map
      (((g3_proj Y N i).left.stalkMap x.underlying).hom.toMonoidHom) (u (p i))
    have he (i : Fin N) : φ i f =
        algebraMap R (g3_power Y N).left.functionField (v i : R) *
          (algebraMap R (g3_power Y N).left.functionField (s2e_curvePowerParameter Y N x i)) ^ n (p i) := by
      rw [hu (p i), map_mul, map_zpow₀]
      simp only [p, Point.underlying_map]
      rw [(hφ i).2 x.underlying, (hφ i).2 x.underlying]
      rfl
    refine ⟨∏ i, v i, ?_⟩
    simp_rw [he]
    rw [Finset.prod_mul_distrib]
    congr 1
    exact (map_prod ((algebraMap R (g3_power Y N).left.functionField).toMonoidHom.comp
      (Units.coeHom R)) v Finset.univ).symm

end HodgeLean.Foundations.Program

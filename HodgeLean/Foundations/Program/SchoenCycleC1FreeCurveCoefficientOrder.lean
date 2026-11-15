import HodgeLean.Foundations.Program.SchoenCycleC1FreeCurveParameter
import HodgeLean.Foundations.Program.SchoenCycleC1GenericLocalFieldSquare
import HodgeLean.Foundations.Program.SchoenCycleC1KummerRamificationOrders

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The specified native downstairs signed order at a free curve point is
divisible by the original Kummer degree.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_c1_free_curve_coefficient_order_dvd
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim X.left = 1) (hdimY : TopologicalSpace.dim Y.left = 1)
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (hinj : Function.Injective a)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (horbit : ∀ x z : ComplexPoint X, Point.map q x = Point.map q z ↔
      ∃ u, Point.map (a u) x = z)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint X) (hx : x.underlying ∈ q.left ⁻¹ᵁ U)
    (hfree : ∀ g, Point.map (a g) x = x → g = 1)
    (hgeneric : q.left (genericPoint X.left) = genericPoint Y.left)
    (f : Y.left.functionField) (z : X.left.functionField) (hz : z ≠ 0)
    (m : ℕ) (v : (Y.left.presheaf.stalk (Point.map q x).underlying)ˣ) (b : ℤ)
    (hf : letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
      f = algebraMap _ Y.left.functionField (v : Y.left.presheaf.stalk (Point.map q x).underlying) *
        algebraMap _ Y.left.functionField
          (s2e_native_curve_parameter Y (Point.map q x)) ^ b)
    (hpower : z ^ m =
      (eqToHom (congrArg Y.left.presheaf.stalk hgeneric.symm) ≫
        q.left.stalkMap (genericPoint X.left)).hom f) :
    (m : ℤ) ∣ b := by
  letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdim]; infer_instance
  letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
  letI := s2e_smooth_curve_point_stalk_dvr X x
  obtain ⟨r, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (s2e_native_curve_parameter_irreducible X x) hz
  have hu' : z = algebraMap _ X.left.functionField (u : X.left.presheaf.stalk x.underlying) *
      algebraMap _ X.left.functionField (s2e_native_curve_parameter X x) ^ r := by
    simpa only [Units.smul_def, Algebra.smul_def] using hu
  obtain ⟨w, hw⟩ := s2e_c1_free_curve_projection_parameter
    X Y hdim hdimY G a ha1 hamul hinj q hsurj hinv horbit U hU x hx hfree
  have hram : (q.left.stalkMap x.underlying).hom
      (s2e_native_curve_parameter Y (Point.map q x)) =
      (w : _) * s2e_native_curve_parameter X x ^ 1 := by
    simpa only [pow_one] using hw
  have hrel := s2e_c1_kummer_ramification_order_relation
    (q.left.stalkMap x.underlying).hom _
    (s2e_c1_generic_stalk_map_local_square q.left hgeneric x.underlying)
    _ _ (s2e_native_curve_parameter_irreducible X x)
    1 w hram f z m v u b r hf hu' hpower
  exact ⟨r, by simpa only [Nat.cast_one, one_mul] using hrel.symm⟩

end HodgeLean.Foundations.Program

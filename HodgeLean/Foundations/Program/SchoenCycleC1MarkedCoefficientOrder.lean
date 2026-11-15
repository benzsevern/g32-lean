import HodgeLean.Foundations.Program.SchoenCycleC1MarkedRamification
import HodgeLean.Foundations.Program.SchoenCycleC1GenericLocalFieldSquare
import HodgeLean.Foundations.Program.SchoenCycleC1KummerRamificationOrders

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual marked projection constructs a downstairs Kummer coefficient order
and relates it to the upstairs signed order using the specified generic field map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_c1_marked_kummer_coefficient_order
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim X.left = 1)
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (hinj : Function.Injective a)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (horbit : ∀ x z : ComplexPoint X, Point.map q x = Point.map q z ↔
      ∃ u, Point.map (a u) x = z)
    (T : Type) [TopologicalSpace T] [ChartedSpace ℂ T] [MulAction G T]
    (e : T ≃ ComplexPoint X) (he : ∀ g t, Point.map (a g) (e t) = e (g • t))
    (t : T) (g : G) (hg : b4_IsRotGen ℂ t g)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (hx : (e t).underlying ∈ q.left ⁻¹ᵁ U)
    (hgeneric : q.left (genericPoint X.left) = genericPoint Y.left)
    (f : Y.left.functionField) (hf : f ≠ 0) (z : X.left.functionField) (m : ℕ)
    (u : (X.left.presheaf.stalk (e t).underlying)ˣ) (r : ℤ)
    (hz : letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdim]; infer_instance
      z = algebraMap (X.left.presheaf.stalk (e t).underlying) X.left.functionField
        (u : X.left.presheaf.stalk (e t).underlying) *
      algebraMap (X.left.presheaf.stalk (e t).underlying) X.left.functionField
        (s2e_native_curve_parameter X (e t)) ^ r)
    (hpower : z ^ m =
      (eqToHom (congrArg Y.left.presheaf.stalk hgeneric.symm) ≫
        q.left.stalkMap (genericPoint X.left)).hom f) :
    letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
    let R := Y.left.presheaf.stalk (q.left (e t).underlying)
    ∃ (v : Rˣ) (b : ℤ),
      f = algebraMap R Y.left.functionField (v : R) *
        algebraMap R Y.left.functionField
          (s2e_native_curve_parameter Y (Point.map q (e t))) ^ b ∧
      (m : ℤ) * r = (orderOf g : ℤ) * b := by
  letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdim]; infer_instance
  letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
  letI := s2e_smooth_curve_point_stalk_dvr X (e t)
  letI : IsDiscreteValuationRing (Y.left.presheaf.stalk (q.left (e t).underlying)) := by
    simpa only [Point.underlying_map] using
      s2e_smooth_curve_point_stalk_dvr Y (Point.map q (e t))
  letI := s2e_smooth_curve_point_stalk_dvr Y (Point.map q (e t))
  have ht := s2e_native_curve_parameter_irreducible Y (Point.map q (e t))
  obtain ⟨b, v, hv⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible ht hf
  have hv' : f = algebraMap (Y.left.presheaf.stalk (Point.map q (e t)).underlying) Y.left.functionField
      (v : Y.left.presheaf.stalk (Point.map q (e t)).underlying) *
      algebraMap _ Y.left.functionField
        (s2e_native_curve_parameter Y (Point.map q (e t))) ^ b := by
    simpa only [Units.smul_def, Algebra.smul_def] using hv
  obtain ⟨w, hw⟩ := s2e_c1_marked_curve_projection_ramification
    X Y hdim hdimY G a ha1 hamul hinj q hsurj hinv horbit T e he t g hg U hU hx
  refine ⟨v, b, hv', ?_⟩
  exact s2e_c1_kummer_ramification_order_relation
    (q.left.stalkMap (e t).underlying).hom _
    (s2e_c1_generic_stalk_map_local_square q.left hgeneric (e t).underlying)
    _ _ (s2e_native_curve_parameter_irreducible X (e t))
    (orderOf g) w hw f z m v u b r hv' hz hpower

end HodgeLean.Foundations.Program

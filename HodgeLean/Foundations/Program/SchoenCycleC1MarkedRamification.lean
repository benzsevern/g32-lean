import HodgeLean.Foundations.Program.SchoenCycleC1MarkedFormalPower
import HodgeLean.Foundations.Program.SchoenCycleC1AlgebraicRamificationFromFormal
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues
import HodgeLean.Foundations.Program.SchoenCycleNativeCurveParameter

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual marked projection pulls back each native base parameter to a unit
 times the native source parameter raised to the marked stabilizer order.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_c1_marked_curve_projection_ramification
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
    (hx : (e t).underlying ∈ q.left ⁻¹ᵁ U) :
    letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdim]; infer_instance
    letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
    ∃ w : (X.left.presheaf.stalk (e t).underlying)ˣ,
      (q.left.stalkMap (e t).underlying).hom
        (s2e_native_curve_parameter Y (Point.map q (e t))) =
      (w : X.left.presheaf.stalk (e t).underlying) *
        s2e_native_curve_parameter X (e t) ^ orderOf g := by
  letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdim]; infer_instance
  letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
  letI := s2e_smooth_curve_point_stalk_dvr X (e t)
  letI : IsDiscreteValuationRing (Y.left.presheaf.stalk (q.left (e t).underlying)) := by
    simpa only [Point.underlying_map] using
      s2e_smooth_curve_point_stalk_dvr Y (Point.map q (e t))
  letI : Algebra ℂ (X.left.presheaf.stalk (e t).underlying) :=
    (HodgeLean.Foundations.Curves.stalkC (e t).underlying).toAlgebra
  letI : Algebra ℂ (Y.left.presheaf.stalk (q.left (e t).underlying)) :=
    (HodgeLean.Foundations.Curves.stalkC (q.left (e t).underlying)).toAlgebra
  obtain ⟨hn, u, ER, ES, hp, hf⟩ := s2e_c1_marked_curve_projection_formal_power
    X Y hdim G a ha1 hamul hinj q hsurj hinv horbit T e he t g hg U hU hx
  exact s2e_c1_algebraic_ramification_of_formal_power
    (q.left.stalkMap (e t).underlying).hom
    (s2e_formal_stalk_pullback X Y q (e t).underlying).toRingHom
    (fun r => s2e_adic_algebra_map_of _ _ _ _ r)
    ES.toRingEquiv ER.toRingEquiv (orderOf g) (Nat.pos_of_ne_zero hn) hf
    _ (s2e_native_curve_parameter_irreducible Y (Point.map q (e t)))
    _ (s2e_native_curve_parameter_irreducible X (e t))

end HodgeLean.Foundations.Program

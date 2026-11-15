import HodgeLean.Foundations.Program.SchoenCycleC1RetainedCurveFormalPower
import HodgeLean.Foundations.Program.SchoenCycleQuotientPointPrimeStabilizer
import HodgeLean.Foundations.Program.SchoenCycleC1AlgebraicRamificationFromFormal
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues

/-! # Actual formal pullback at a free orbit point -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- At an actual free curve point, the original base native parameter
pulls back to a unit times the original source native parameter. -/
theorem s2e_c1_free_curve_projection_parameter
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
    (hfree : ∀ g, Point.map (a g) x = x → g = 1) :
    letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdim]; infer_instance
    letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
    ∃ w : (X.left.presheaf.stalk x.underlying)ˣ,
      (q.left.stalkMap x.underlying).hom (s2e_native_curve_parameter Y (Point.map q x)) =
        (w : _) * s2e_native_curve_parameter X x := by
  letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdim]; infer_instance
  letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
  letI := s2e_smooth_curve_point_stalk_dvr X x
  letI : IsDiscreteValuationRing (Y.left.presheaf.stalk (q.left x.underlying)) := by
    simpa only [Point.underlying_map] using s2e_smooth_curve_point_stalk_dvr Y (Point.map q x)
  letI : Algebra ℂ (X.left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI : Algebra ℂ (Y.left.presheaf.stalk (q.left x.underlying)) :=
    (HodgeLean.Foundations.Curves.stalkC (q.left x.underlying)).toAlgebra
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  let P := ((hU.preimage q.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal
  let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
  let H := MulAction.stabilizer G o
  have hone (g : H) : g.val = 1 := by
    apply hfree
    apply (s2e_quotient_point_prime_stabilizer X Y G a ha1 hamul q hinv U hU x hx g.val).mp
    exact congrArg Subtype.val g.property
  letI : Subsingleton H := ⟨fun g h => Subtype.ext ((hone g).trans (hone h).symm)⟩
  have hc : Nat.card H = 1 := Nat.card_unique
  obtain ⟨u, ER, ES, _, hf⟩ := s2e_c1_retained_curve_projection_formal_power
    X Y hdim G a ha1 hamul hinj q hsurj hinv horbit U hU x hx
  have he (f) : s2e_formal_stalk_pullback X Y q x.underlying (ES f) =
      ER (PowerSeries.expand 1 (by decide) f) := by
    have ht := hf f
    change s2e_formal_stalk_pullback X Y q x.underlying (ES f) =
      ER (PowerSeries.expand (Nat.card H) Nat.card_pos.ne' f) at ht
    simpa only [hc] using ht
  obtain ⟨w, hw⟩ := s2e_c1_algebraic_ramification_of_formal_power
    (q.left.stalkMap x.underlying).hom
    (s2e_formal_stalk_pullback X Y q x.underlying).toRingHom
    (fun r => s2e_adic_algebra_map_of _ _ _ _ r)
    ES.toRingEquiv ER.toRingEquiv 1 (by decide) he
    _ (s2e_native_curve_parameter_irreducible Y (Point.map q x))
    _ (s2e_native_curve_parameter_irreducible X x)
  exact ⟨w, by simpa only [pow_one] using hw⟩

end HodgeLean.Foundations.Program

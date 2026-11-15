import HodgeLean.Foundations.Program.SchoenCycleC1RetainedCurveFormalPower
import HodgeLean.Foundations.Program.SchoenCycleC1MarkedPrimeStabilizerOrder
import HodgeLean.Foundations.Program.SchoenCycleC11DegreeHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-! # Formal power coordinates under the retained curve hypotheses -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The formal exponent of the actual curve projection is the order of the
specified marked rotation generator. -/
theorem s2e_c1_marked_curve_projection_formal_power
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    (hdim : TopologicalSpace.dim X.left = 1)
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
    let S := Y.left.presheaf.stalk (q.left (e t).underlying)
    letI : Algebra ℂ S := (HodgeLean.Foundations.Curves.stalkC (q.left (e t).underlying)).toAlgebra
    let R := X.left.presheaf.stalk (e t).underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC (e t).underlying).toAlgebra
    ∃ hn : orderOf g ≠ 0, ∃ u : Rˣ,
    ∃ ER : PowerSeries ℂ ≃ₐ[ℂ] AdicCompletion (IsLocalRing.maximalIdeal R) R,
    ∃ ES : PowerSeries ℂ ≃ₐ[ℂ] AdicCompletion (IsLocalRing.maximalIdeal S) S,
      (∀ p : Polynomial ℂ, ER (p : PowerSeries ℂ) = AdicCompletion.of _ _
        (Polynomial.aeval (s2e_native_curve_parameter X (e t) * (u : R)) p)) ∧
      ∀ f, s2e_formal_stalk_pullback X Y q (e t).underlying (ES f) =
        ER (PowerSeries.expand (orderOf g) hn f) := by
  letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdim]; infer_instance
  have hc := s2e_c1_marked_prime_stabilizer_card X Y G a ha1 hamul q hinv T e he U hU t hx
  obtain ⟨u, ER, ES, hp, hf⟩ := s2e_c1_retained_curve_projection_formal_power
    X Y hdim G a ha1 hamul hinj q hsurj hinv horbit U hU (e t) hx
  have hn : orderOf g ≠ 0 := by rw [hg.2.1]; exact Nat.card_pos.ne'
  refine ⟨hn, u, ER, ES, hp, ?_⟩
  intro f
  simpa only [hc, ← hg.2.1] using hf f

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCycleC1RetainedCurveFormalPower
import HodgeLean.Foundations.Program.SchoenCycleQuotientPointPrimeStabilizer

/-! # Actual formal pullback at a free orbit point -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- At a point with trivial actual deck stabilizer, the actual formal stalk
pullback is bijective. -/
theorem s2e_c1_free_point_formal_pullback_bijective
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
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint X) (hx : x.underlying ∈ q.left ⁻¹ᵁ U)
    (hfree : ∀ g, Point.map (a g) x = x → g = 1) :
    Function.Bijective (s2e_formal_stalk_pullback X Y q x.underlying) := by
  letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdim]; infer_instance
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
  have he (f) : s2e_formal_stalk_pullback X Y q x.underlying (ES f) = ER f := by
    have ht := hf f
    change s2e_formal_stalk_pullback X Y q x.underlying (ES f) =
      ER (PowerSeries.expand (Nat.card H) Nat.card_pos.ne' f) at ht
    simpa only [hc, PowerSeries.expand_one_apply] using ht
  constructor
  · intro v w hvw
    obtain ⟨v, rfl⟩ := ES.surjective v
    obtain ⟨w, rfl⟩ := ES.surjective w
    rw [he, he] at hvw
    exact congrArg ES (ER.injective hvw)
  · intro z
    obtain ⟨f, rfl⟩ := ER.surjective z
    exact ⟨ES f, he f⟩

end HodgeLean.Foundations.Program

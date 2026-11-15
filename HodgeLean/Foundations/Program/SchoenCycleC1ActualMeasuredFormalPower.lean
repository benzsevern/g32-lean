import HodgeLean.Foundations.Program.SchoenCycleC1MeasuredFormalPowerEquation
import HodgeLean.Foundations.Program.SchoenCycleC1ActualGenericDeckRepresentation

/-! # Formal power coordinates from actual deck maps and their measured degree -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual faithful curve deck maps and their measured degree determine
formal power coordinates for the actual projection, with source parameter
values and the entire formal stalk pullback retained. -/
theorem s2e_c1_actual_measured_cover_formal_power_equation
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (hinj : Function.Injective a)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hg : q.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [Nonempty (q.left ⁻¹ᵁ U)] [IsIntegrallyClosed Γ(Y.left, U)]
    (x : ComplexPoint X) (hx : x.underlying ∈ q.left ⁻¹ᵁ U)
    (hcx : IsClosed ({x.underlying} : Set X.left))
    (hcy : IsClosed ({q.left x.underlying} : Set Y.left)) :
    letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      q.left.stalkMap (genericPoint X.left)).hom
    letI := φ.toAlgebra
    ∀ [Module.Finite Y.left.functionField X.left.functionField], Module.finrank Y.left.functionField X.left.functionField = Nat.card G →
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    let P := ((hU.preimage q.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal
    let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
    let H := MulAction.stabilizer G o
    let S := Y.left.presheaf.stalk (q.left x.underlying)
    letI : Algebra ℂ S := (HodgeLean.Foundations.Curves.stalkC (q.left x.underlying)).toAlgebra
    let R := X.left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ u : Rˣ,
    ∃ ER : PowerSeries ℂ ≃ₐ[ℂ] AdicCompletion (IsLocalRing.maximalIdeal R) R,
    ∃ ES : PowerSeries ℂ ≃ₐ[ℂ] AdicCompletion (IsLocalRing.maximalIdeal S) S,
      (∀ p : Polynomial ℂ, ER (p : PowerSeries ℂ) = AdicCompletion.of _ _
        (Polynomial.aeval (s2e_native_curve_parameter X x * (u : R)) p)) ∧
      ∀ f, s2e_formal_stalk_pullback X Y q x.underlying (ES f) =
        ER (PowerSeries.expand (Nat.card H) Nat.card_pos.ne' f) := by
  letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  dsimp only
  intro hfinite hdeg
  letI := hfinite
  obtain ⟨ρ, hρ, hρval⟩ := s2e_c1_actual_generic_deck_representation
    X Y G a ha1 hamul hinj q hinv hg
  exact s2e_c1_measured_actual_formal_power_equation
    X Y G a ha1 hamul hinj q hinv hg U hU x hx hcx hcy ρ hρ hdeg hρval

end HodgeLean.Foundations.Program

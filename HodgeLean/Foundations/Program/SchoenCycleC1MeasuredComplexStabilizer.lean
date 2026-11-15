import HodgeLean.Foundations.Program.SchoenCycleC1MeasuredAdicStabilizer
import HodgeLean.Foundations.Program.SchoenCycleQuotientAdicStabilizer
import HodgeLean.Foundations.Program.SchoenCycleComplexSectionTower
import HodgeLean.Foundations.Program.SchoenCycleInvariantScalarRestriction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Measured generic deck data retain the actual complex formal section map
under the prime stabilizer invariant comparison. -/
theorem s2e_c1_measured_complex_adic_stabilizer_values
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsLocallyNoetherian X.left] [IsIntegral Y.left]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [IsDominant q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hg : q.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [Nonempty (q.left ⁻¹ᵁ U)] [IsIntegrallyClosed Γ(Y.left, U)]
    (p : Ideal Γ(Y.left, U)) [p.IsMaximal]
    (I : Ideal Γ(X.left, q.left ⁻¹ᵁ U)) [I.IsPrime] :
    letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      q.left.stalkMap (genericPoint X.left)).hom
    letI := φ.toAlgebra
    ∀ [Module.Finite Y.left.functionField X.left.functionField]
      (ρ : G →* (X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField)),
      Function.Injective ρ → Module.finrank Y.left.functionField X.left.functionField = Nat.card G →
      (∀ g, (ρ g).toRingHom = s2e_step1_fieldPullback X.left (a g⁻¹).left) →
    letI := s2e_step1_sectionAlgebra Y U
    letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
    letI : Algebra Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := (q.left.app U).hom.toAlgebra
    letI : IsScalarTower ℂ Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := s2e_complex_section_app_tower X Y q U
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_quotient_sectionAction_base_smulComm X Y G a ha1 hamul q hinv U
    let α := MulSemiringAction.toAlgAut G Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U)
    let o : MulAction.orbit G I := ⟨I, MulAction.mem_orbit_self I⟩
    let β (g : MulAction.stabilizer G o) := s2e_adic_algebra_map I I ((α g.val).toAlgHom.restrictScalars ℂ)
      (s2e_orbit_ideal_stabilizer_preserves_powers G Γ(X.left, q.left ⁻¹ᵁ U) I g)
    ∀ hI : I.LiesOver p,
    letI := hI
    ∃ F : AdicCompletion p Γ(Y.left, U) ≃ₐ[ℂ]
      (⨅ g : MulAction.stabilizer G o, AlgHom.equalizer (β g)
        (AlgHom.id ℂ (AdicCompletion I Γ(X.left, q.left ⁻¹ᵁ U))) :
        Subalgebra ℂ (AdicCompletion I Γ(X.left, q.left ⁻¹ᵁ U))),
      ∀ x, (F x).val = s2e_adic_algebra_map p I
        ((Algebra.ofId Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U)).restrictScalars ℂ)
        (fun n a ha => (Ideal.pow_right_mono
          (Ideal.map_le_iff_le_comap.mpr (Ideal.over_def I p).le) n)
          (s2e_base_map_preserves_extended_ideal_powers p n a ha)) x := by
  letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  dsimp only
  intro hfinite ρ hρ hdeg hρval
  letI := hfinite
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X W
  letI : Algebra Γ(Y.left, U) Γ(X.left, W) := (q.left.app U).hom.toAlgebra
  letI : IsScalarTower ℂ Γ(Y.left, U) Γ(X.left, W) := s2e_complex_section_app_tower X Y q U
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_quotient_sectionAction_base_smulComm X Y G a ha1 hamul q hinv U
  intro hI
  letI := hI
  obtain ⟨E, hE⟩ := s2e_c1_measured_adic_stabilizer_values X Y G a ha1 hamul q hinv hg U hU
    ρ hρ hdeg hρval p I
  refine ⟨(E.restrictScalars ℂ).trans (s2e_invariant_restrict_scalars_equiv (k := ℂ) _), ?_⟩
  intro x
  exact hE x

end HodgeLean.Foundations.Program

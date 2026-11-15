import HodgeLean.Foundations.Program.SchoenCycleC1MeasuredInvariantExtension
import HodgeLean.Foundations.Program.SchoenCycleAdicBaseStabilizer

/-! # Measured deck descent to a retained formal prime factor -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The measured generic deck representation identifies the actual base
formal ring with one retained prime stabilizer invariant ring, retaining
all canonical formal section values. -/
theorem s2e_c1_measured_adic_stabilizer_values
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsLocallyNoetherian X.left] [IsIntegral Y.left]
    (G : Type) [Group G] [Fintype G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (q : X ⟶ Y) [IsFinite q.left] [IsDominant q.left] (hinv : ∀ g, a g ≫ q = q)
    (hg : q.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [Nonempty (q.left ⁻¹ᵁ U)] [IsIntegrallyClosed Γ(Y.left, U)] :
    letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      q.left.stalkMap (genericPoint X.left)).hom
    letI := φ.toAlgebra
    letI := s2e_step1_sectionAlgebra Y U
    letI : Algebra Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := (q.left.app U).hom.toAlgebra
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_quotient_sectionAction_base_smulComm X Y G a ha1 hamul q hinv U
    ∀ [Module.Finite Y.left.functionField X.left.functionField]
      (ρ : G →* (X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField)),
      Function.Injective ρ → Module.finrank Y.left.functionField X.left.functionField = Nat.card G →
      (∀ g, (ρ g).toRingHom = s2e_step1_fieldPullback X.left (a g⁻¹).left) →
      ∀ (p : Ideal Γ(Y.left, U)) [p.IsMaximal]
        (I : Ideal Γ(X.left, q.left ⁻¹ᵁ U)) [I.IsPrime] [I.LiesOver p],
      let R := Γ(Y.left, U)
      let B := Γ(X.left, q.left ⁻¹ᵁ U)
      let α := MulSemiringAction.toAlgAut G R B
      let o : MulAction.orbit G I := ⟨I, MulAction.mem_orbit_self I⟩
      let β (g : MulAction.stabilizer G o) := s2e_adic_algebra_map I I (α g.val).toAlgHom
        (s2e_orbit_ideal_stabilizer_preserves_powers G B I g)
      ∃ F : AdicCompletion p R ≃ₐ[R]
        (⨅ g : MulAction.stabilizer G o, AlgHom.equalizer (β g)
          (AlgHom.id R (AdicCompletion I B)) : Subalgebra R (AdicCompletion I B)),
        ∀ z, (F z).val = s2e_adic_algebra_map p I (Algebra.ofId R B)
          (fun n b hb => (Ideal.pow_right_mono
            (Ideal.map_le_iff_le_comap.mpr (Ideal.over_def I p).le) n)
            (s2e_base_map_preserves_extended_ideal_powers p n b hb)) z := by
  letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  letI := s2e_step1_sectionAlgebra Y U
  letI : Algebra Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := (q.left.app U).hom.toAlgebra
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_quotient_sectionAction_base_smulComm X Y G a ha1 hamul q hinv U
  dsimp only
  intro hfinite ρ hρ hdeg hρval p hp I hprime hI
  letI := hfinite
  letI := hp
  letI := hprime
  letI := hI
  letI := s2e_c1_measured_section_invariant_extension X Y G a ha1 hamul q hinv hg U hU
    ρ hρ hdeg hρval
  letI : IsNoetherianRing Γ(X.left, q.left ⁻¹ᵁ U) :=
    IsLocallyNoetherian.component_noetherian ⟨q.left ⁻¹ᵁ U, hU.preimage q.left⟩
  letI := IsSchemeTheoreticallyDominant.of_isDominant q.left
  exact s2e_adic_base_stabilizer_comparison Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) G
    (q.left.app_injective U) p I

end HodgeLean.Foundations.Program

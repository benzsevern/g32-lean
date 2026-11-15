import HodgeLean.Foundations.Program.SchoenTowerBranchProjectiveCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Actual point addition between the specified projective symmetric quotients is an immersion.
Source: Schoen (1988), printed p. 12; SGA 1, Exposé V, §1, invariant affine quotient charts. -/
theorem s2t_branch_projective_immersion_aux (C P B : Over (Spec ↧ℂ))
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (n : ℕ) (b : ComplexPoint C)
    (π : g3_power C n ⟶ P) (γ : g3_power C (n + 1) ⟶ B)
    (hπinv : ∀ σ, s2_permute C n σ ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγinv : ∀ σ, s2_permute C (n + 1) σ ≫ γ = γ)
    (hγquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (n + 1) ⟶ T),
      (∀ σ, s2_permute C (n + 1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (a : P ⟶ B) (ha : π ≫ a = s2c_branchInsertion C n b ≫ γ) :
    IsClosedImmersion a.left := by
  letI : IsAffine (terminal Scheme.{0}) :=
    IsAffine.of_isIso (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).inv
  letI : IsSeparated (terminal.from (g3_power C (n + 1)).left) := by
    rw [← terminal.comp_from (g3_power C (n + 1)).hom]
    infer_instance
  have hs := (s2t_retained_quotient_orbits (g3_power C (n + 1)) B
    (Equiv.Perm (Fin (n + 1))) (s2_symmetricPowerAction C (n + 1)) γ hγinv hγquot).1
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsClosedImmersion)
  intro y
  obtain ⟨x, hx⟩ := hs y
  let points : Option (Fin (n + 1)) → C.left :=
    fun i => i.elim (Point.underlying b) (fun j => (g3_proj C (n + 1) j).left x)
  obtain ⟨U, hU, hm⟩ := s2_projective_commonAffineOpen ℂ C.left C.hom
    (Option (Fin (n + 1))) points
  let bU : ComplexPoint (openScheme C U) := asOpenPoint C U b (hm none)
  have hb : bU ≫ openInclusion C U = b := by
    apply Over.OverMorphism.ext
    exact liftToOpen_fac C U b (hm none)
  have haU : π ≫ a = s2c_branchInsertion C n (bU ≫ openInclusion C U) ≫ γ := by
    rw [hb]
    exact ha
  obtain ⟨V, hV, hclosed⟩ := s2t_branch_projective_chart C P B n U hU bU π γ
    hπinv hπquot hγinv hγquot a haU
  refine ⟨V, ?_, hclosed⟩
  rw [← hx]
  change x ∈ γ.left ⁻¹' (V : Set B.left)
  rw [hV, s2t_powerOpen_range]
  exact fun i => hm (some i)

end HodgeLean.Foundations.Program

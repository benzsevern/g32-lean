import HodgeLean.Foundations.Program.SchoenCycleMixedExactFixedFunctionModelCotangent
import HodgeLean.Foundations.Program.SchoenCycleMixedStabilizerEtaleRealization
import HodgeLean.Foundations.Program.SchoenCycleEtaleSectionPullbackValues
import HodgeLean.Foundations.Program.SchoenCycleMixedExactFixedFunctionCotangent
import HodgeLean.Foundations.Program.SchoenCycleIdentifiedPrimeEtaleSections
import HodgeLean.Foundations.Program.SchoenCycleSubalgebraEvaluationPoint
import HodgeLean.Foundations.Program.SchoenCycleAdicRenameEquiv
import HodgeLean.Foundations.Program.SchoenCycleFormalCoordinateFunctionBasis
import HodgeLean.Foundations.Program.SchoenCycleComplexFixedFunctionNoetherian
import HodgeLean.Foundations.Program.SchoenCycleMixedExactFixedFunctionCoordinates
import HodgeLean.Foundations.Program.SchoenCycleFixedFunctionFiniteType
import HodgeLean.Foundations.Program.SchoenCycleComplexAffineFiniteType
import HodgeLean.Foundations.Program.SchoenCycleMixedExactFixedFunctionGerms
import HodgeLean.Foundations.Program.SchoenCycleMixedExactStalkInvariants
import HodgeLean.Foundations.Program.SchoenCycleComplexFixedFunctionLocalDescent
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric
import HodgeLean.Foundations.Program.SchoenCycleComplexLocalFixedFunctionFormalStalk
import HodgeLean.Foundations.Program.SchoenCycleMixedInverseStalkInvariantCoordinates
import HodgeLean.Foundations.Program.SchoenCycleMixedInverseStalkInvariantValues
import HodgeLean.Foundations.Program.SchoenCycleExactInvariantCotangentBasis

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Exact mixed elementary functions are actual etale section germs on the stabilizer affine scheme, with canonical affine values and their original geometric pullbacks retained.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8; EGA IV, 17.11.1. -/
theorem s2e_mixed_stabilizer_etale_sections
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z n ⟶ B) (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (U : B.left.Opens) (hW : IsAffineOpen (γ.left ⁻¹ᵁ U))
    (x : ComplexPoint (g3_power Z n)) (hxU : x.underlying ∈ γ.left ⁻¹ᵁ U)
    (b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    (hcx : IsClosed ({x.underlying} : Set (g3_power Z n).left)) :
    let H := s2e_powerPointStabilizer Z n x
    letI : Fintype H := Fintype.ofFinite H
    let a := fun σ : H => s2_permute Z n σ.val
    let ha1 : a 1 = 𝟙 (g3_power Z n) := s2e_step1_permute_one Z n
    let hamul : ∀ u v, a (u * v) = a v ≫ a u := fun u v => s2e_step1_permute_mul Z n u.val v.val
    let hinv := fun σ : H => hγ σ.val
    let hfix := fun σ : H => s2e_complex_point_fixed_underlying (g3_power Z n)
      (a σ) x σ.property
    let W := γ.left ⁻¹ᵁ U
    letI := s2e_step1_sectionAlgebra (g3_power Z n) W
    letI := s2e_step1_sectionAction (g3_power Z n) B H a ha1 hamul γ hinv U
    letI := s2e_step1_sectionAction_smulComm (g3_power Z n) B H a ha1 hamul γ hinv U
    let P := (hW.primeIdealOf ⟨x.underlying, hxU⟩).asIdeal
    let S := FixedPoints.subalgebra ℂ Γ((g3_power Z n).left, W) H
    let Q := P.under S
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    let XS := Over.mk (ComplexPoint.affineSpecStructureMap S)
    ∃ (z : ComplexPoint XS),
      z.underlying.asIdeal = Q ∧
      ∃ f : XS.left.presheaf.stalk z.underlying →+* R,
        (∀ s : S, f ((XS.left.presheaf.germ ⊤ z.underlying trivial).hom
          ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) =
            ((g3_power Z n).left.presheaf.germ W x.underlying hxU).hom s.val) ∧
        ∃ (V : XS.left.Opens) (_ : IsAffineOpen V) (hzV : z.underlying ∈ V),
          letI := s2e_step1_sectionAlgebra XS V
          ∃ G : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(XS.left, V),
            G.toRingHom.Etale ∧
            ∀ a (j : Fin (m a)), f ((XS.left.presheaf.germ V z.underlying hzV).hom
              (G (X (ι ⟨a, j⟩)))) =
                aeval (s2e_curvePowerParameter Z n x)
                  (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m (X ⟨a, j⟩)).val) := by
  dsimp only
  let H := s2e_powerPointStabilizer Z n x
  letI : Fintype H := Fintype.ofFinite H
  let a := fun σ : H => s2_permute Z n σ.val
  let ha1 : a 1 = 𝟙 (g3_power Z n) := s2e_step1_permute_one Z n
  let hamul : ∀ u v, a (u * v) = a v ≫ a u := fun u v => s2e_step1_permute_mul Z n u.val v.val
  let hinv := fun σ : H => hγ σ.val
  let hfix := fun σ : H => s2e_complex_point_fixed_underlying (g3_power Z n) (a σ) x σ.property
  letI : IsLocallyNoetherian (g3_power Z n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power Z n).hom
  letI : Algebra ℂ ((g3_power Z n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let W := γ.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra (g3_power Z n) W
  letI := s2e_step1_sectionAction (g3_power Z n) B H a ha1 hamul γ hinv U
  letI := s2e_step1_sectionAction_smulComm (g3_power Z n) B H a ha1 hamul γ hinv U
  let P := (hW.primeIdealOf ⟨x.underlying, hxU⟩).asIdeal
  let S := FixedPoints.subalgebra ℂ Γ((g3_power Z n).left, W) H
  let Q := P.under S
  obtain ⟨E, c, hc, D, hD, hval⟩ := s2e_mixed_exact_fixed_function_formal_cotangent_basis
    Z B n γ hγ U hW x hxU b m ι p hp hx hcx
  have hbFin (i : Fin n) : (D.reindex ι) i =
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent
        ⟨c (ι.symm i), hc (ι.symm i)⟩ := by
    rw [Module.Basis.reindex_apply]
    exact hD (ι.symm i)
  let f0 := @s2e_complex_fixed_function_local_pullback (g3_power Z n) B inferInstance (s2e_powerPointStabilizer Z n x)
    inferInstance (Fintype.ofFinite (s2e_powerPointStabilizer Z n x))
    (fun σ => s2_permute Z n σ.val) (s2e_step1_permute_one Z n)
    (fun u v => s2e_step1_permute_mul Z n u.val v.val) γ (fun σ => hγ σ.val)
    U hW x.underlying hxU (fun σ => s2e_complex_point_fixed_underlying
      (g3_power Z n) (s2_permute Z n σ.val) x σ.property)
  have hf0 (s : S) : f0 (algebraMap S (Localization.AtPrime Q) s) =
      ((g3_power Z n).left.presheaf.germ W x.underlying hxU).hom s.val :=
    @s2e_complex_fixed_function_local_pullback_of (g3_power Z n) B inferInstance (s2e_powerPointStabilizer Z n x)
    inferInstance (Fintype.ofFinite (s2e_powerPointStabilizer Z n x))
    (fun σ => s2_permute Z n σ.val) (s2e_step1_permute_one Z n)
    (fun u v => s2e_step1_permute_mul Z n u.val v.val) γ (fun σ => hγ σ.val)
    U hW x.underlying hxU (fun σ => s2e_complex_point_fixed_underlying
      (g3_power Z n) (s2_permute Z n σ.val) x σ.property) s
  apply s2e_mixed_stabilizer_etale_realization Z B n γ hγ U hW x hxU b m ι p hp hx hcx f0 hf0
    (E.trans (s2e_adic_rename_equiv (R := ℂ) ι))
    (c ∘ ι.symm) (fun i => hc (ι.symm i)) (D.reindex ι) hbFin
  intro l j
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  convert hval ⟨l, j⟩ using 2 <;> rfl

#print axioms s2e_mixed_stabilizer_etale_sections
end HodgeLean.Foundations.Program

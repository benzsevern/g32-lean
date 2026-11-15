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

/-- Supplied exact mixed elementary cotangent functions and a formal model are realized on the actual stabilizer affine scheme, retaining canonical affine values and geometric pullbacks.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8; EGA IV, 17.11.1. -/
theorem s2e_mixed_stabilizer_etale_realization
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
    ∀ (f0 : Localization.AtPrime Q →ₐ[ℂ] R)
      (hf0 : ∀ s : S, f0 (algebraMap S (Localization.AtPrime Q) s) =
        ((g3_power Z n).left.presheaf.germ W x.underlying hxU).hom s.val)
      (E : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (Localization.AtPrime Q) ≃ₐ[ℂ]
        AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
      (c : Fin n → Localization.AtPrime Q)
      (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (D : Module.Basis (Fin n) ℂ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).Cotangent)
      (hD : ∀ i, D i = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent ⟨c i, hc i⟩)
      (hval : ∀ l (j : Fin (m l)),
        f0 (c (ι ⟨l, j⟩)) =
        aeval (s2e_curvePowerParameter Z n x)
          (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m (X ⟨l, j⟩)).val)),
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
  intro f0 hf0 E c hc D hD hval
  letI : Nonempty W := ⟨⟨x.underlying, hxU⟩⟩
  letI : IsDomain Γ((g3_power Z n).left, W) := IsIntegral.component_integral W
  letI : IsDomain S := inferInstance
  letI : Algebra.FiniteType ℂ Γ((g3_power Z n).left, W) :=
    s2e_complex_affine_sections_finiteType (g3_power Z n) W hW
  letI : Algebra.FiniteType ℂ S := s2e_fixed_function_finiteType ℂ _ H
  have hxBound : ⊤ ≤ x.left ⁻¹ᵁ W := by
    intro t ht
    have he : t = IsLocalRing.closedPoint ℂ :=
      @Subsingleton.elim (PrimeSpectrum ℂ) inferInstance t (IsLocalRing.closedPoint ℂ)
    subst t
    exact hxU
  let ε := (s2e_step1_pointEvaluation (g3_power Z n) W x hxBound).comp S.val
  let z := (ComplexPoint.affineSpecEquiv S).symm ε
  have hzQ : z.underlying.asIdeal = Q :=
    s2e_subalgebra_evaluation_point_prime (g3_power Z n) W hW x hxBound S
  let q0 (i : Fin n) := aeval (s2e_curvePowerParameter Z n x)
    (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m (X (ι.symm i))).val)
  obtain ⟨F, hF, V, hV, hzV, G, het, hG⟩ :=
    s2e_etale_section_pullback_values S _ n z Q hzQ f0 q0
      ⟨E, c, hc, D, hD,
        (fun i => by
          obtain ⟨⟨l, j⟩, rfl⟩ := ι.surjective i
          simpa only [q0, Equiv.symm_apply_apply] using hval l j)⟩
  refine ⟨z, hzQ, F, ?_, V, hV, hzV, G, het, ?_⟩
  · intro s
    exact (hF s).trans (hf0 s)
  · intro l j
    simpa only [q0, Equiv.symm_apply_apply] using hG (ι ⟨l, j⟩)

#print axioms s2e_mixed_stabilizer_etale_realization
end HodgeLean.Foundations.Program

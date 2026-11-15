import HodgeLean.Foundations.Program.SchoenCycleMixedStabilizerEtaleSections
import HodgeLean.Foundations.Program.SchoenCycleMixedElementaryParameterNonunit
import HodgeLean.Foundations.Program.SchoenCycleSectionVanishingPullback

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Exact mixed elementary sections on the actual stabilizer neighbourhood vanish at the actual marked point while retaining every canonical affine and geometric pullback value.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_mixed_stabilizer_centered_etale_sections
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
            (∀ i, Point.evaluate V (G (X i)) z = 0) ∧
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
  obtain ⟨z, hz, f, hf, V, hV, hzV, G, hG, hval⟩ :=
    s2e_mixed_stabilizer_etale_sections Z B n γ hγ U hW x hxU b m ι p hp hx hcx
  let XS := Over.mk (ComplexPoint.affineSpecStructureMap S)
  let R := (g3_power Z n).left.presheaf.stalk x.underlying
  letI : Nonempty W := ⟨⟨x.underlying, hxU⟩⟩
  letI : IsDomain Γ((g3_power Z n).left, W) := IsIntegral.component_integral W
  letI : IsDomain S := inferInstance
  letI : IsIntegral XS.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of S)))
  refine ⟨z, hz, f, hf, V, hV, hzV, G, hG, ?_, hval⟩
  intro i
  obtain ⟨⟨a, j⟩, rfl⟩ := ι.surjective i
  apply s2e_section_evaluate_zero_of_nonunit_pullback XS z V hzV _ R f
  rw [hval a j]
  exact s2e_mixed_elementary_parameter_nonunit Z n x b m ι a j

#print axioms s2e_mixed_stabilizer_centered_etale_sections
end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenTowerL1bKummerQuotientField
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerDegree
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerActionPowers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A categorical quotient by one finite-cover symmetry has cyclic Galois
function-field degree equal to the symmetry's order. -/
theorem s2v_l1b_generator_quotient_degree
    {S : Scheme.{0}} (X Y : Over S) [IsIntegral X.left] [IsIntegral Y.left]
    [IsSeparated X.hom]
    (f : X ⟶ Y) [IsFinite f.left] [IsDominant f.left]
    (d : X ⟶ X) [IsIso d] (hd : d ≫ f = f)
    (hcat : ∀ (T : Over S) (g : X ⟶ T), d ≫ g = g → ∃! u : Y ⟶ T, f ≫ u = g)
    (U : Y.left.affineOpens) [Nonempty U.1] :
    letI := (s2v_l1b_functionFieldPullback f.left).hom.toAlgebra
    Module.Finite Y.left.functionField X.left.functionField ∧
    IsGalois Y.left.functionField X.left.functionField ∧
    IsCyclic (X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField) ∧
    Module.finrank Y.left.functionField X.left.functionField = orderOf (End.of d) := by
  letI := (s2v_l1b_functionFieldPullback f.left).hom.toAlgebra
  haveI : Module.Finite Y.left.functionField X.left.functionField :=
    s2v_l1b_functionFieldPullback_finite f.left
  obtain ⟨τ, hτ⟩ := s2v_l1b_cover_field_algEquiv f.left d.left
    (congrArg Over.Hom.left hd)
  have hfix : IntermediateField.fixedField (Subgroup.zpowers τ) = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    have hzτ : τ z = z :=
      (IntermediateField.mem_fixedField_iff (Subgroup.zpowers τ) z).mp hz τ (Subgroup.mem_zpowers τ)
    obtain ⟨c, hc⟩ := s2v_l1b_categorical_quotient_fixed_rational_function X Y f
      (fun _ : Unit => d) (fun _ => hd)
      (fun T g hg => hcat T g (hg ())) U (fun _ => τ) (fun _ => hτ) z (fun _ => hzτ)
    exact IntermediateField.mem_bot.mpr ⟨c, hc⟩
  obtain ⟨hgal, hcyc, hdegree⟩ := s2v_l1b_degree_of_fixed_generator
    Y.left.functionField X.left.functionField τ hfix
  let E := X.left.functionField
  let F := Y.left.functionField
  let embed : (E ≃ₐ[F] E) →* End E :=
    { toFun := fun u => End.of (CommRingCat.ofHom u.toRingHom)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hemb : Function.Injective embed := by
    intro u v huv
    apply AlgEquiv.ext
    intro z
    exact congrArg (fun k : End E => k.asHom z) huv
  have hsquare : Spec.map (embed τ).asHom ≫ X.left.fromSpecStalk (genericPoint X.left) =
      X.left.fromSpecStalk (genericPoint X.left) ≫ d.left := by
    change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ _ = _
    rw [hτ]
    exact s2v_l1b_functionFieldPullback_generic_square d.left
  have hgeneric := s2v_l1b_generic_order_eq X.hom (embed τ) (End.of d.left) (Over.w d) hsquare
  have hforget : orderOf (End.of d.left) = orderOf (End.of d) := by
    apply orderOf_injective ((Over.forget S).mapEnd X) _ (End.of d)
    intro u v huv
    apply End.ext
    apply Over.OverMorphism.ext
    exact congrArg End.asHom huv
  exact ⟨inferInstance, hgal, hcyc, hdegree.trans
    ((orderOf_injective embed hemb τ).symm.trans (hgeneric.trans hforget))⟩

end HodgeLean.Foundations.Program

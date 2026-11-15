import HodgeLean.Foundations.Program.SchoenTowerL1bKummerQuotientField
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerGenericAction
import Mathlib.FieldTheory.Galois.IsGaloisGroup

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A faithful finite cyclic categorical quotient has its group's order as actual function-field degree. -/
theorem s2v_l1b_cyclic_categorical_quotient_degree
    {S : Scheme.{0}} (X Y : Over S) [IsIntegral X.left] [IsIntegral Y.left]
    [IsSeparated X.hom]
    (G : Type) [Group G] [Finite G] [IsCyclic G]
    (ρ : G →* Aut X) (hinj : Function.Injective ρ)
    (f : X ⟶ Y) [IsFinite f.left] [IsDominant f.left]
    (hinv : ∀ g, (ρ g).asIso.hom ≫ f = f)
    (hcat : ∀ (T : Over S) (g : X ⟶ T),
      (∀ i, (ρ i).asIso.hom ≫ g = g) → ∃! u : Y ⟶ T, f ≫ u = g)
    (U : Y.left.affineOpens) [Nonempty U.1] :
    letI := (s2v_l1b_functionFieldPullback f.left).hom.toAlgebra
    Module.Finite Y.left.functionField X.left.functionField ∧
    IsGalois Y.left.functionField X.left.functionField ∧
    IsCyclic (X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField) ∧
    Module.finrank Y.left.functionField X.left.functionField = Nat.card G := by
  letI := (s2v_l1b_functionFieldPullback f.left).hom.toAlgebra
  let ρs := ((Over.forget S).mapAut X).comp ρ
  letI := s2v_l1b_functionFieldAction X.left G ρs
  have hρs : Function.Injective ρs := by
    intro g k h
    apply hinj
    apply Aut.ext
    apply Iso.ext
    apply Over.OverMorphism.ext
    exact congrArg (fun u : Aut X.left => u.asIso.hom) h
  haveI : FaithfulSMul G X.left.functionField :=
    s2v_l1b_functionFieldAction_faithful X.hom G ρs hρs
      (fun g => Over.w (ρ g).asIso.hom)
  have hfix (g : G) (c : Y.left.functionField) :
      g • s2v_l1b_functionFieldPullback f.left c = s2v_l1b_functionFieldPullback f.left c :=
    s2v_l1b_functionFieldAction_fixes_base f.left G ρs
      (fun g => congrArg Over.Hom.left (hinv g)) g c
  haveI : SMulCommClass G Y.left.functionField X.left.functionField := by
    refine ⟨?_⟩
    intro g c z
    change g • (s2v_l1b_functionFieldPullback f.left c * z) =
      s2v_l1b_functionFieldPullback f.left c * (g • z)
    rw [smul_mul', hfix]
  let τ := MulSemiringAction.toAlgAut G Y.left.functionField X.left.functionField
  haveI : IsGaloisGroup G Y.left.functionField X.left.functionField := by
    refine ⟨inferInstance, inferInstance, ⟨?_⟩⟩
    intro z hz
    apply s2v_l1b_categorical_quotient_fixed_rational_function X Y f
      (fun g : G => (ρ g⁻¹).asIso.hom) (fun g => hinv g⁻¹) ?_ U
      (fun g => τ g) (fun _ => rfl) z hz
    intro T g hg
    apply hcat T g
    intro i
    simpa only [inv_inv] using hg i⁻¹
  haveI : Module.Finite Y.left.functionField X.left.functionField :=
    IsGaloisGroup.finiteDimensional G Y.left.functionField X.left.functionField
  haveI : IsGalois Y.left.functionField X.left.functionField :=
    IsGaloisGroup.isGalois G Y.left.functionField X.left.functionField
  haveI : IsCyclic (X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField) :=
    isCyclic_of_surjective
      (IsGaloisGroup.mulEquivAlgEquiv G Y.left.functionField X.left.functionField).toMonoidHom
      (IsGaloisGroup.mulEquivAlgEquiv G Y.left.functionField X.left.functionField).surjective
  exact ⟨inferInstance, inferInstance, inferInstance,
    (IsGaloisGroup.card_eq_finrank G Y.left.functionField X.left.functionField).symm⟩

end HodgeLean.Foundations.Program

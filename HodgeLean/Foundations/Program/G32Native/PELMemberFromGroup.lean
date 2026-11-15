import HodgeLean.Foundations.Program.G32Native.GeneralTypeIIIDefs
import HodgeLean.Foundations.Program.G32Native.PELGenericGroupLie
import HodgeLean.Foundations.Abdulali.SkewCentralizerBaseChange

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Abdulali
namespace HodgeLean.Foundations.Program.GeneralTypeIII

private theorem commutes_basis_iff {D V : Type*} [Ring D] [Algebra ℚ D]
    [AddCommGroup V] [Module ℚ V] (e : Module.Basis (Fin 4) ℚ D)
    (f : D →ₗ[ℚ] Module.End ℚ V) (X : Module.End ℚ V) :
    (∀ i, X * f (e i) = f (e i) * X) ↔ ∀ d, X * f d = f d * X := by
  constructor
  · intro h
    let F : D →ₗ[ℚ] Module.End ℚ V :=
      (LinearMap.mulRight ℚ X - LinearMap.mulLeft ℚ X).comp f
    have hF : F = 0 := by
      apply e.ext
      intro i
      exact sub_eq_zero.mpr (h i).symm
    intro d
    exact (sub_eq_zero.mp (LinearMap.congr_fun hF d)).symm
  · intro h i
    exact h (e i)

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite
variable
  (W : HodgeBlocks.WeilAction
    (abelianVarietyCohomologyOf (finiteBetti_abelian A)
      (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
      (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2) (h : SixfoldData A W pol)

/-- Assemble the shared type-III record from an exact endomorphism presentation,
its Rosati equation, and the algebraic generic-group tangent calculation.
The latter calculation is an explicit input, rather than the native rational
Hodge Lie equality. The four-operator centralizer is expanded to all rational
endomorphisms using the retained algebra equivalence.
Source: Abdulali, Annals 155 (2002), Proposition 2.3.1 and §§3.1–3.3;
Abdulali, International Journal of Mathematics 10 (1999), §2.5;
Borel, Linear Algebraic Groups, second edition, §3.5. -/
def generalPELMember_of_group
    (b : ℚ) (hb : b < 0) (end0 : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A)
    (heisenstein : W.J = (abelianEnd0Action A (end0 ⟨0, 1, 0, 0⟩)).unop)
    (hadj : ∀ d x y,
      polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate
        ((abelianEnd0Action A (end0 d)).unop x) y =
      polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate x
        ((abelianEnd0Action A (end0 (star d))).unop y))
    {n : ℕ} (basis : Module.Basis (Fin n) ℚ (HQ A 1))
    (G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (hGroup : g2_hodgeGroup
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.H
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.isInternal basis = G)
    (hTangent : g1_lieOfSet G =
      (complexSpan (skewCentralizerOfFamily
        (polarizationForm (torusCohomology_cupProductOf A) h.nondegenerate)
        (fun i => (abelianEnd0Action A
          (end0 (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i))).unop))).map
        (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ basis)
          (Algebra.TensorProduct.basis ℂ basis)).toLinearMap) :
    GeneralPELMember A W pol h where
  b := b
  b_neg := hb
  end0 := end0
  eisenstein := heisenstein
  rosati := hadj
  general := by
    have hLie := hodgeLie_of_generic_group _ _ basis G _ hGroup hTangent
    change (↑((hodgeLieAlgebra (V := HQ A 1) _ _).toSubmodule) : Set (Module.End ℚ (HQ A 1))) = _
    rw [hLie]
    ext X
    rw [SetLike.mem_coe, mem_skewCentralizerOfFamily]
    let f : ℍ[ℚ, -3, 0, b] →ₗ[ℚ] Module.End ℚ (HQ A 1) :=
      { toFun := fun q => (abelianEnd0Action A (end0 q)).unop
        map_add' := by intros; simp
        map_smul' := by intros; simp }
    have hc := commutes_basis_iff (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b) f X
    constructor
    · rintro ⟨hs, hcomm⟩
      refine ⟨hs, ?_⟩
      intro d
      obtain ⟨q, rfl⟩ := end0.surjective d
      exact hc.mp hcomm q
    · rintro ⟨hs, hcomm⟩
      exact ⟨hs, hc.mpr (fun q => hcomm (end0 q))⟩

#print axioms commutes_basis_iff
#print axioms generalPELMember_of_group
end HodgeLean.Foundations.Program.GeneralTypeIII

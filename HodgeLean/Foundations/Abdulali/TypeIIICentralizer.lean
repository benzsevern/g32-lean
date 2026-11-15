import HodgeLean.Foundations.Abdulali.RationalCentralizer
import HodgeLean.Foundations.Program.G32Native.TypeIIIPaperDefs

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program.TypeIIIPaper

namespace HodgeLean.Foundations.Abdulali

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

local instance : Module.Finite ℚ (HQ A 1) :=
  (torusCohomology_cupProductOf A).finite

variable
  (W : letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)
  (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)


/-- The covariant rational quaternion representation obtained from the
contravariant cohomology action by quaternion conjugation.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.1–3.2 and §4. -/
def typeIIIQuaternionAction (P : GeneralPELMember A W pol hM) :
    ℍ[ℚ, -3, 0, P.b] →ₐ[ℚ] Module.End ℚ (HQ A 1) where
  toFun q := (abelianEnd0Action A (P.end0 (star q))).unop
  map_one' := by simp
  map_zero' := by simp
  map_add' q r := by simp
  map_mul' q r := by simp
  commutes' q := by
    have hs : star (algebraMap ℚ ℍ[ℚ, -3, 0, P.b] q) =
        algebraMap ℚ ℍ[ℚ, -3, 0, P.b] q := by
      ext <;> simp [QuaternionAlgebra.algebraMap_eq]
    change (abelianEnd0Action A (P.end0 (star (algebraMap ℚ ℍ[ℚ, -3, 0, P.b] q)))).unop = _
    rw [hs]
    rw [P.end0.commutes, (abelianEnd0Action A).commutes]
    rfl

example (P : GeneralPELMember A W pol hM) (q : ℍ[ℚ, -3, 0, P.b]) :
    typeIIIQuaternionAction A W pol hM P q =
      (abelianEnd0Action A (P.end0 (star q))).unop := rfl

/-- The covariant quaternion generator is the negative of the selected
Eisenstein operator. This records the contravariance sign explicitly.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.2 and §4;
the selected quadratic action is the field `P.eisenstein`. -/
theorem typeIIIQuaternionAction_eisenstein (P : GeneralPELMember A W pol hM) :
    typeIIIQuaternionAction A W pol hM P ⟨0, 1, 0, 0⟩ = -W.J := by
  have hI : star (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, P.b]) = -⟨0, 1, 0, 0⟩ := by
    ext <;> simp
  rw [P.eisenstein]
  change (abelianEnd0Action A (P.end0 (star _))).unop = _
  rw [hI, map_neg, map_neg]
  rfl

private theorem centralizer_basis_iff {Q U : Type*} [Ring Q] [Algebra ℚ Q]
    [AddCommGroup U] [Module ℚ U] {κ : Type*} [Fintype κ]
    (B : Module.Basis κ ℚ Q) (ρ : Q →ₐ[ℚ] Module.End ℚ U) (X : Module.End ℚ U) :
    (∀ i, X * ρ (B i) = ρ (B i) * X) ↔ ∀ q, X * ρ q = ρ q * X := by
  constructor
  · intro h
    let F : Q →ₗ[ℚ] Module.End ℚ U :=
      (LinearMap.mulRight ℚ X - LinearMap.mulLeft ℚ X).comp ρ.toLinearMap
    have hF : F = 0 := by
      apply B.ext
      intro i
      exact sub_eq_zero.mpr (h i).symm
    intro q
    exact (sub_eq_zero.mp (LinearMap.congr_fun hF q)).symm
  · intro h i; exact h (B i)

/-- The general PEL datum's exact rational Hodge Lie algebra is the finite
quaternion skew-centralizer used by the scalar-extension calculation.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.2 and §4;
the general-member equality is retained as the field `P.general`. -/
theorem typeIII_hodgeLie_eq_skewCentralizer (P : GeneralPELMember A W pol hM) :
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian A)
      (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
      (torusCohomology_cupProductOf A)
    (hodgeLieAlgebra S.weight1.H S.weight1.isInternal).toSubmodule =
      skewCentralizerOfFamily
        (polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate)
        (fun i => typeIIIQuaternionAction A W pol hM P
          (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 P.b i)) := by
  dsimp only
  ext X
  have hg : X ∈ (hodgeLieAlgebra
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.H
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.isInternal).toSubmodule ↔
      (∀ x y, polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate (X x) y +
        polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate x (X y) = 0) ∧
      ∀ d : AbelianEnd0 A, X.comp (abelianEnd0Action A d).unop =
        (abelianEnd0Action A d).unop.comp X := by
    exact Set.ext_iff.mp P.general X
  rw [hg, mem_skewCentralizerOfFamily, centralizer_basis_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h q
    exact h (P.end0 (star q))
  · intro h d
    have hh := h (star (P.end0.symm d))
    change X * (abelianEnd0Action A (P.end0 (star (star (P.end0.symm d))))).unop =
      (abelianEnd0Action A (P.end0 (star (star (P.end0.symm d))))).unop * X at hh
    simpa only [star_star, P.end0.apply_symm_apply, Module.End.mul_eq_comp] using hh

/-- The complexified general type-III PEL Hodge Lie algebra is the orthogonal
Lie algebra on a six-dimensional multiplicity factor. The construction keeps
the Rosati involution, the polarization, the selected Eisenstein generator
and the actual complexified rational Lie algebra.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.1–3.2 and §4, p. 923;
Shimura, Annals of Mathematics 78 (1963), Propositions 15 and 17. -/
theorem typeIII_skew_centralizer_normal_form (P : GeneralPELMember A W pol hM) :
    let ρ := typeIIIQuaternionAction A W pol hM P
    let E := polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian A)
      (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
      (torusCohomology_cupProductOf A)
    ∃ (s : ℂ) (a : ℍ[ℂ, -3, 0, (P.b : ℂ)] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
      (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1))
      (B : LinearMap.BilinForm ℂ (Fin 6 → ℂ)),
      s ^ 2 = -3 ∧ (∀ q, a (star q) = (a q).adjugate) ∧
      a ⟨0, 1, 0, 0⟩ = !![s, 0; 0, -s] ∧ B.IsSymm ∧ B.Nondegenerate ∧
      ρ ⟨0, 1, 0, 0⟩ = -W.J ∧
      (∀ q z, quaternionComplexAction P.b ρ q (e z) =
        e ((Matrix.toLin' (a q)).rTensor (Fin 6 → ℂ) z)) ∧
      (∀ (x y : Fin 2 → ℂ) (u v : Fin 6 → ℂ),
        E.baseChange ℂ (e (x ⊗ₜ[ℂ] u)) (e (y ⊗ₜ[ℂ] v)) =
          (x 0 * y 1 - x 1 * y 0) * B u v) ∧
      ∀ X : Module.End ℂ (ℂ ⊗[ℚ] HQ A 1),
        X ∈ complexSpan (hodgeLieAlgebra S.weight1.H S.weight1.isInternal).toSubmodule ↔
        ∃! T : Module.End ℂ (Fin 6 → ℂ),
          (∀ u v, B (T u) v + B u (T v) = 0) ∧
          e.symm.conj X = T.lTensor (Fin 2 → ℂ) := by
  dsimp only
  have hdim : Module.finrank ℚ (HQ A 1) = 12 := by
    rw [(torusCohomology_cupProductOf A).finrank_eq, hM.dim_eq]
  have hRosati : ∀ q z w,
      polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate
        (typeIIIQuaternionAction A W pol hM P q z) w =
      polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate z
        (typeIIIQuaternionAction A W pol hM P (star q) w) := by
    intro q z w
    change polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate
        ((abelianEnd0Action A (P.end0 (star q))).unop z) w =
      polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate z
        ((abelianEnd0Action A (P.end0 (star (star q)))).unop w)
    simpa only [star_star] using P.rosati (star q) z w
  obtain ⟨s, a, e, B, hs, ha, hI, hsym, hB, he, hform, hcentral⟩ :=
    rational_quaternion_skew_centralizer hdim P.b (ne_of_lt P.b_neg)
      (typeIIIQuaternionAction A W pol hM P)
      (polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate)
      (isAlt_polarizationForm _ _) (nondegenerate_polarizationForm _ _) hRosati
  refine ⟨s, a, e, B, hs, ha, hI, hsym, hB,
    typeIIIQuaternionAction_eisenstein A W pol hM P, he, hform, ?_⟩
  intro X
  rw [typeIII_hodgeLie_eq_skewCentralizer A W pol hM P]
  exact hcentral X

end HodgeLean.Foundations.Abdulali

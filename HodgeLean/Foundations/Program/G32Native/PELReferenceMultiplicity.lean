import HodgeLean.Foundations.Program.G32Native.PELReferenceQuaternionAction
import HodgeLean.Foundations.Program.G32Native.PELMultiplicityCenter

noncomputable section
set_option maxHeartbeats 400000
open scoped Quaternion TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Abdulali
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The reference datum has an orthogonal six-dimensional multiplicity
factor independently of any general-member equality. -/
theorem pelReferenceMultiplicity (R : PELSplitReference) :
    let ρ := pelReferenceQuaternionAction R
    let E := polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate
    ∃ (s : ℂ) (a : ℍ[ℂ, -3, 0, (R.b : ℂ)] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
      (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ R.B.X 1))
      (B : LinearMap.BilinForm ℂ (Fin 6 → ℂ)),
      s ^ 2 = -3 ∧ (∀ q, a (star q) = (a q).adjugate) ∧
      a ⟨0, 1, 0, 0⟩ = !![s, 0; 0, -s] ∧ B.IsSymm ∧ B.Nondegenerate ∧
      (∀ q z, quaternionComplexAction R.b ρ q (e z) =
        e ((Matrix.toLin' (a q)).rTensor (Fin 6 → ℂ) z)) ∧
      (∀ (x y : Fin 2 → ℂ) (u v : Fin 6 → ℂ),
        E.baseChange ℂ (e (x ⊗ₜ[ℂ] u)) (e (y ⊗ₜ[ℂ] v)) =
          (x 0 * y 1 - x 1 * y 0) * B u v) ∧
      ∀ X : Module.End ℂ (ℂ ⊗[ℚ] HQ R.B.X 1),
        X ∈ complexSpan (skewCentralizerOfFamily E
          (fun i => ρ (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))) ↔
        ∃! T : Module.End ℂ (Fin 6 → ℂ),
          (∀ u v, B (T u) v + B u (T v) = 0) ∧
          e.symm.conj X = T.lTensor (Fin 2 → ℂ) := by
  letI := (torusCohomology_cupProductOf R.B.X).finite
  have hdim : Module.finrank ℚ (HQ R.B.X 1) = 12 := by
    rw [Module.finrank_eq_card_basis R.basis]
    rfl
  exact rational_quaternion_skew_centralizer hdim R.b (ne_of_lt R.b_neg)
    (pelReferenceQuaternionAction R)
    (polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate)
    (isAlt_polarizationForm _ _) (nondegenerate_polarizationForm _ _)
    (pelReferenceQuaternionAction_rosati R)

#print axioms pelReferenceMultiplicity
/-- The reference quaternionic skew-centralizer has zero centre, without
any general-member premise.
Source: `rational_quaternion_skew_centralizer` and
`pel_multiplicity_center_eq_zero`. -/
theorem pel_reference_skew_center_eq_zero (R : PELSplitReference)
    (J : Module.End ℂ (ℂ ⊗[ℚ] HQ R.B.X 1))
    (hJ : J ∈ complexSpan (skewCentralizerOfFamily
      (polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate)
      (fun i => pelReferenceQuaternionAction R
        (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))))
    (hc : ∀ X ∈ complexSpan (skewCentralizerOfFamily
      (polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate)
      (fun i => pelReferenceQuaternionAction R
        (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))), J * X = X * J) :
    J = 0 := by
  letI := (torusCohomology_cupProductOf R.B.X).finite
  let E := polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate
  have hdim : Module.finrank ℚ (HQ R.B.X 1) = 12 := by
    simpa using Module.finrank_eq_card_basis R.basis
  have hadj : ∀ q x y, E (pelReferenceQuaternionAction R q x) y =
      E x (pelReferenceQuaternionAction R (star q) y) := by
    intro q x y
    change E ((abelianEnd0Action R.B.X (R.end0 (star q))).unop x) y =
      E x ((abelianEnd0Action R.B.X (R.end0 (star (star q)))).unop y)
    simpa only [star_star] using R.adjoint (star q) x y
  obtain ⟨s, a, e, B, hs, ha, hI, hsym, hB, he, hform, hnormal⟩ :=
    rational_quaternion_skew_centralizer hdim R.b (ne_of_lt R.b_neg)
      (pelReferenceQuaternionAction R) E (isAlt_polarizationForm _ _)
      (nondegenerate_polarizationForm _ _) hadj
  exact pel_multiplicity_center_eq_zero _ e B hsym hB hnormal J hJ hc

#print axioms pelReferenceQuaternionAction
#print axioms pel_reference_skew_center_eq_zero
end HodgeLean.Foundations.Program.GeneralTypeIII

import HodgeLean.Foundations.Program.G32Native.PELReferenceMultiplicity
import HodgeLean.Foundations.Program.G32Native.PELGenericTangentBaseChange

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations.Abdulali

private theorem pel_commutes_basis {D V : Type*} [AddCommGroup D] [Module ℚ D]
    [AddCommGroup V] [Module ℚ V] {ι : Type*} (b : Module.Basis ι ℚ D)
    (f : D →ₗ[ℚ] Module.End ℚ V) (X : Module.End ℚ V) :
    (∀ i, X * f (b i) = f (b i) * X) ↔ ∀ d, X * f d = f d * X := by
  constructor
  · intro h
    let F := (LinearMap.mulRight ℚ X - LinearMap.mulLeft ℚ X).comp f
    have hF : F = 0 := by
      apply b.ext
      intro i
      exact sub_eq_zero.mpr (h i).symm
    intro d
    exact (sub_eq_zero.mp (LinearMap.congr_fun hF d)).symm
  · intro h i; exact h (b i)

/-- Quaternion conjugation in the cohomological action does not change
its rational skew centralizer. -/
theorem pel_reference_actual_skew_eq (R : PELSplitReference) :
    skewCentralizerOfFamily
      (polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate)
      (fun i => (abelianEnd0Action R.B.X (R.end0
        (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))).unop) =
    skewCentralizerOfFamily
      (polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate)
      (fun i => pelReferenceQuaternionAction R
        (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)) := by
  let f : ℍ[ℚ, -3, 0, R.b] →ₗ[ℚ] Module.End ℚ (HQ R.B.X 1) :=
    { toFun := fun q => (abelianEnd0Action R.B.X (R.end0 q)).unop
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  ext X
  rw [mem_skewCentralizerOfFamily, mem_skewCentralizerOfFamily]
  change (_ ∧ ∀ i, X * f _ = f _ * X) ↔
    (_ ∧ ∀ i, X * (pelReferenceQuaternionAction R).toLinearMap _ =
      (pelReferenceQuaternionAction R).toLinearMap _ * X)
  rw [pel_commutes_basis _ f, pel_commutes_basis _ (pelReferenceQuaternionAction R).toLinearMap]
  apply and_congr_right
  intro _
  constructor
  · intro h q
    exact h (star q)
  · intro h q
    have hh := h (star q)
    change X * f (star (star q)) = f (star (star q)) * X at hh
    simpa only [star_star] using hh

/-- The Lie centre of the reference connected isometry group is zero.
Source: `pel_reference_skew_center_eq_zero` and `pelGenericGroup_tangent`. -/
theorem pel_reference_lie_center_eq_zero (R : PELSplitReference)
    (M : Matrix (Fin 12) (Fin 12) ℂ)
    (hM : M ∈ g1_lieOfSet (pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℂ))))
    (hc : ∀ X ∈ g1_lieOfSet (pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℂ))),
      M * X = X * M) : M = 0 := by
  letI := (torusCohomology_cupProductOf R.B.X).finite
  let E := polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate
  let F := fun i : Fin 4 => (abelianEnd0Action R.B.X
    (R.end0 (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))).unop
  let c := Algebra.TensorProduct.basis ℂ R.basis
  let L := complexSpan (skewCentralizerOfFamily E F)
  have hform : LinearMap.toMatrix₂ c c (E.baseChange ℂ) =
      R.form.map (algebraMap ℚ ℂ) := by
    ext i j
    simp only [c, PELSplitReference.form, E, LinearMap.toMatrix₂_apply,
      Algebra.TensorProduct.basis_apply, LinearMap.BilinForm.baseChange_tmul,
      one_mul, Matrix.map_apply, Algebra.smul_def, mul_one]
  have ht := pelGenericGroup_tangent R.basis E F
  rw [hform] at ht
  simp only [LinearMap.toMatrix_baseChange] at ht
  change g1_lieOfSet (pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
    (Set.range fun i : Fin 4 =>
      (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℂ))) =
    L.map (LinearMap.toMatrix c c).toLinearMap at ht
  rw [ht] at hM
  obtain ⟨J, hJ, hJM⟩ := hM
  have hJM' : LinearMap.toMatrix c c J = M := hJM
  have hJc : ∀ X ∈ L, J * X = X * J := by
    intro X hX
    have hmX : LinearMap.toMatrix c c X ∈ L.map (LinearMap.toMatrix c c).toLinearMap :=
      ⟨X, hX, rfl⟩
    rw [← ht] at hmX
    have hh := hc _ hmX
    apply (LinearMap.toMatrix c c).injective
    simpa only [LinearMap.toMatrix_mul, hJM'] using hh
  have hJ0 : J = 0 := by
    apply pel_reference_skew_center_eq_zero R J
    · change J ∈ complexSpan (skewCentralizerOfFamily E F) at hJ
      dsimp only [F, E] at hJ
      rw [pel_reference_actual_skew_eq] at hJ
      exact hJ
    · dsimp only [L, F, E] at hJc
      rw [pel_reference_actual_skew_eq] at hJc
      exact hJc
  rw [hJ0, map_zero] at hJM
  exact hJM.symm

#print axioms pel_reference_actual_skew_eq
#print axioms pel_reference_lie_center_eq_zero
end HodgeLean.Foundations.Program.GeneralTypeIII

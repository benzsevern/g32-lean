import HodgeLean.Foundations.PositivePolarizationDefs
import HodgeLean.Foundations.PositivePolarizationModel
import HodgeLean.Foundations.PositivePolarizationConj
import HodgeLean.Adapters.GagaWiring
import HodgeLean.Foundations.PositivePolarizationRosati

/-! # Proof obligations for the positive-polarization specification -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Module
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Symplectic NumberField

namespace HodgeLean.Foundations

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

theorem p1_isNondegenerate_of_isPositive_aux {ω : ⋀[ℚ]^2 V}
    {I : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V} (h : p1_IsPositive ω I) : IsNondegenerate ω :=
  p1l_isNondegenerate_of_isPositive h

theorem p1_dualForm_adjoint_aux {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω)
    (f : Module.End ℚ V) (x y : V) :
    dualForm hω (f x) y = dualForm hω x (p1_adjoint ω hω f y) := by
  simp [dualForm_apply, p1_adjoint, LinearMap.dualMap_apply]

theorem p1_trace_pos_aux {ω : ⋀[ℚ]^2 V} {I : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V}
    (h : p1_IsPositive ω I) (hI : I ∘ₗ I = -LinearMap.id) {f : Module.End ℚ V}
    (hf : f.baseChange ℝ ∘ₗ I = I ∘ₗ f.baseChange ℝ) (hf0 : f ≠ 0) :
    0 < LinearMap.trace ℚ V (f ∘ₗ p1_adjoint ω (p1_isNondegenerate_of_isPositive_aux h) f) :=
  p1l_trace_pos h hI hf hf0 _

end Linear

section Model

theorem p1_isPositive_model_aux : p1_IsPositive p1_modelForm (p1_modelJ.baseChange ℝ) :=
  p1l_isPositive_model

theorem p1_not_isPositive_model_neg_aux :
    IsNondegenerate (-p1_modelForm) ∧ ¬ p1_IsPositive (-p1_modelForm) (p1_modelJ.baseChange ℝ) :=
  p1l_not_isPositive_model_neg

theorem p1_model₄_aux :
    ∃ hω : IsNondegenerate p1_modelForm₄,
      ¬ p1_IsPositive p1_modelForm₄ (p1_modelJ₄.baseChange ℝ) ∧
      p1_modelSwap₄ ∘ₗ p1_modelJ₄ = p1_modelJ₄ ∘ₗ p1_modelSwap₄ ∧ p1_modelSwap₄ ≠ 0 ∧
      LinearMap.trace ℚ (Fin 4 → ℚ) (p1_modelSwap₄ ∘ₗ p1_adjoint p1_modelForm₄ hω p1_modelSwap₄) =
        -4 :=
  p1l_model₄

end Model

section Abelian

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

theorem p1_isPolarization_iff_aux (pol : HQ A 2) :
    p1_IsPolarization A pol ↔
      ∃ hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol),
        PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη := by
  let := (torusCohomology_cupProductOf A).finite
  have hW :=
    spec_weightOneComplexStructure A (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
  constructor
  · intro hP
    have hη := p1_isNondegenerate_of_isPositive_aux hP
    obtain ⟨hinv, hpos⟩ := (p1l_isPositive_iff hη hW.1).1 hP
    refine ⟨hη, (spec_polarizationPositive_iff A _ _ hη).2 ⟨?_, hpos⟩⟩
    exact (spec_firstRiemannRelation A _ _ hη).2
      ⟨(pol1_real_invariant_iff_hodge_isotropic _ _
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ hW.2.1).1 hinv,
        hinv⟩
  · rintro ⟨hη, hPP⟩
    obtain ⟨hHdg, hpos⟩ := (spec_polarizationPositive_iff A _ _ hη).1 hPP
    exact (p1l_isPositive_iff hη hW.1).2 ⟨((spec_firstRiemannRelation A _ _ hη).1 hHdg).2, hpos⟩

theorem p1_mem_hdg_aux {pol : HQ A 2} (hP : p1_IsPolarization A pol) :
    (pol : H^(2 * 1)(A; ℚ)) ∈ Hdg^1(A; ℚ) := by
  obtain ⟨hη, hPP⟩ := (p1_isPolarization_iff_aux A pol).1 hP
  exact ((spec_polarizationPositive_iff A _ _ hη).1 hPP).1

variable [IsCommMonObj A]

theorem p1_adjoint_mem_range_aux {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (φ : AbelianEnd0 A) :
    letI := (torusCohomology_cupProductOf A).finite
    p1_adjoint (polarizationVec (torusCohomology_cupProductOf A) pol)
        (p1_isNondegenerate_of_isPositive_aux hP) (abelianEnd0Action A φ).unop ∈
      Set.range fun ψ : AbelianEnd0 A => (abelianEnd0Action A ψ).unop := by
  let _ := (torusCohomology_cupProductOf A).finite
  exact (p1r_mem_range_iff A _).2 (p1r_adjoint_mem_hodgeEndH1 A _ (p1_mem_hdg_aux A hP)
    (spec_g4_abelianEnd0Action_mem_hodgeEndH1 A φ))

theorem p1_rosati_add_aux {pol : HQ A 2} (hP : p1_IsPolarization A pol) (φ ψ : AbelianEnd0 A) :
    let ρ :=
      p1_rosati A pol (p1_isNondegenerate_of_isPositive_aux hP) (p1_adjoint_mem_range_aux A hP)
    ρ (φ + ψ) = ρ φ + ρ ψ := by
  exact p1r_rosati_add _ _ φ ψ

theorem p1_rosati_smul_aux {pol : HQ A 2} (hP : p1_IsPolarization A pol) (q : ℚ)
    (φ : AbelianEnd0 A) :
    let ρ :=
      p1_rosati A pol (p1_isNondegenerate_of_isPositive_aux hP) (p1_adjoint_mem_range_aux A hP)
    ρ (q • φ) = q • ρ φ := by
  exact p1r_rosati_smul _ _ q φ

theorem p1_rosati_one_aux {pol : HQ A 2} (hP : p1_IsPolarization A pol) :
    let ρ :=
      p1_rosati A pol (p1_isNondegenerate_of_isPositive_aux hP) (p1_adjoint_mem_range_aux A hP)
    ρ 1 = 1 := by
  exact p1r_rosati_one _ _

theorem p1_rosati_mul_aux {pol : HQ A 2} (hP : p1_IsPolarization A pol) (φ ψ : AbelianEnd0 A) :
    let ρ :=
      p1_rosati A pol (p1_isNondegenerate_of_isPositive_aux hP) (p1_adjoint_mem_range_aux A hP)
    ρ (φ * ψ) = ρ ψ * ρ φ := by
  exact p1r_rosati_mul _ _ φ ψ

theorem p1_rosati_rosati_aux {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (φ : AbelianEnd0 A) :
    let ρ :=
      p1_rosati A pol (p1_isNondegenerate_of_isPositive_aux hP) (p1_adjoint_mem_range_aux A hP)
    ρ (ρ φ) = φ := by
  exact p1r_rosati_rosati _ _ φ

theorem p1_rosati_pos_aux {pol : HQ A 2} (hP : p1_IsPolarization A pol) {φ : AbelianEnd0 A}
    (hφ : φ ≠ 0) :
    let ρ :=
      p1_rosati A pol (p1_isNondegenerate_of_isPositive_aux hP) (p1_adjoint_mem_range_aux A hP)
    0 < LinearMap.trace ℚ (HQ A 1) (abelianEnd0Action A (φ * ρ φ)).unop := by
  intro ρ
  let _ := (torusCohomology_cupProductOf A).finite
  have hT := spec_g4_abelianEnd0Action_mem_hodgeEndH1 A φ
  have hI : weightOneComplexStructure A (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A) ∘ₗ
      weightOneComplexStructure A (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A) =
        -LinearMap.id :=
    LinearMap.ext (spec_weightOneComplexStructure A (finiteBetti_abelian A)
      (spec_bettiDeRhamIso_abelian A)).1
  have hT0 : (abelianEnd0Action A φ).unop ≠ 0 := fun h0 =>
    hφ (p1r_unop_abelianEnd0Action_injective A (by simpa using h0))
  have hpos := p1_trace_pos_aux hP hI (p1r_baseChange_comp_weightOneComplexStructure A hT) hT0
  rw [map_mul, MulOpposite.unop_mul, p1r_abelianEnd0Action_rosati, Module.End.mul_eq_comp,
    LinearMap.trace_comp_comm']
  exact hpos

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]

theorem p1_rosati_conj_aux {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (hθ : Function.Bijective θ) (a : L) :
    let ρ :=
      p1_rosati A pol (p1_isNondegenerate_of_isPositive_aux hP) (p1_adjoint_mem_range_aux A hP)
    ρ (θ a) = θ (IsCMField.complexConj L a) := by
  intro ρ
  let _ : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite
  let e := AlgEquiv.ofBijective θ hθ
  -- `σ = θ⁻¹ ∘ ρ ∘ θ`, a ring involution of `L`.
  have hρθ : ∀ x : L, θ (e.symm (ρ (θ x))) = ρ (θ x) := fun x => e.apply_symm_apply _
  have hsymm : ∀ x : L, e.symm (θ x) = x := fun x => e.symm_apply_apply x
  let σ : L →+* L :=
    { toFun := fun x => e.symm (ρ (θ x))
      map_one' := by
        simp only [map_one]
        rw [show ρ 1 = 1 from p1_rosati_one_aux A hP, map_one]
      map_mul' := fun x y => by
        rw [map_mul, show ρ (θ x * θ y) = ρ (θ y) * ρ (θ x) from p1_rosati_mul_aux A hP _ _,
          map_mul, mul_comm]
      map_zero' := by
        have h := p1_rosati_add_aux A hP 0 0
        rw [map_zero, show ρ 0 = 0 from by simpa using h, map_zero]
      map_add' := fun x y => by
        rw [map_add, show ρ (θ x + θ y) = ρ (θ x) + ρ (θ y) from p1_rosati_add_aux A hP _ _,
          map_add] }
  have hσ : ∀ x, θ (σ x) = ρ (θ x) := hρθ
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    change e.symm (ρ (θ (σ x))) = x
    rw [hσ, show ρ (ρ (θ x)) = θ x from p1_rosati_rosati_aux A hP _, hsymm]
  -- The action of `L` on `H¹` and its trace.
  let r : L →ₐ[ℚ] Module.End ℚ (HQ A 1) :=
    { toFun := fun x => (abelianEnd0Action A (θ x)).unop
      map_one' := by simp only [map_one, MulOpposite.unop_one]
      map_mul' := fun x y => by
        rw [mul_comm x y, map_mul, map_mul, MulOpposite.unop_mul]
      map_zero' := by simp only [map_zero, MulOpposite.unop_zero]
      map_add' := fun x y => by simp only [map_add, MulOpposite.unop_add]
      commutes' := fun q => by
        simp only [AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op] }
  obtain ⟨m, hm⟩ := p1c_trace_algHom_eq r
  have hpos : ∀ x : L, x ≠ 0 → 0 < Algebra.trace ℚ L (x * σ x) := by
    intro x hx
    have hθx : θ x ≠ 0 := by
      rw [← map_zero θ]; exact fun h => hx (hθ.1 h)
    have h : 0 < LinearMap.trace ℚ (HQ A 1) (abelianEnd0Action A (θ x * ρ (θ x))).unop :=
      p1_rosati_pos_aux A hP hθx
    rw [show ρ (θ x) = θ (σ x) from (hσ x).symm, ← map_mul] at h
    change 0 < LinearMap.trace ℚ (HQ A 1) (r (x * σ x)) at h
    rw [hm, nsmul_eq_mul] at h
    exact pos_of_mul_pos_right h (Nat.cast_nonneg m)
  rw [← hσ, p1c_eq_complexConj σ hσσ hpos]

end Abelian

end HodgeLean.Foundations

import HodgeLean.Foundations.Program.MilnePowerGrading
import HodgeLean.Foundations.Program.MilneDivisorsLinear
import Mathlib.LinearAlgebra.BilinearForm.Properties

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

def m2_formOperator {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : LinearMap.BilinForm K V) (d : ⋀[K]^2 V) : Module.End K V :=
  contract d ∘ₗ E.flip

theorem m2_form_fixed_iff_commutes {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (E : LinearMap.BilinForm K V)
    (hE : E.Nondegenerate) (d : ⋀[K]^2 V) (u : Module.End K V)
    (hu : Function.Surjective u) (hiso : ∀ x y, E (u x) (u y) = E x y) :
    exteriorPower.map 2 u d = d ↔
      u ∘ₗ m2_formOperator E d = m2_formOperator E d ∘ₗ u := by
  have he (x : V) : u.dualMap (E.flip (u x)) = E.flip x := by
    apply LinearMap.ext
    intro y
    exact hiso y x
  have hs : Function.Surjective E.flip := (E.flip.toDual hE.flip).surjective
  constructor
  · intro hd
    have hh := congrArg contract hd
    rw [contract_map] at hh
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun hh (E.flip (u x))
    simpa only [LinearMap.comp_apply, he, m2_formOperator] using h
  · intro hc
    apply contract_injective
    rw [contract_map]
    apply LinearMap.ext
    intro φ
    obtain ⟨x, rfl⟩ := hs φ
    obtain ⟨y, rfl⟩ := hu x
    simpa only [LinearMap.comp_apply, he, m2_formOperator] using
      LinearMap.congr_fun hc y


theorem m2_form_derivation_iff_commutes {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (E : LinearMap.BilinForm K V) (hE : E.Nondegenerate) (d : ⋀[K]^2 V)
    (f : Module.End K V) (hf : ∀ x y, E (f x) y = -E x (f y)) :
    InvariantsExterior.exteriorDer 2 f d = 0 ↔
      f ∘ₗ m2_formOperator E d = m2_formOperator E d ∘ₗ f := by
  have he (x : V) : f.dualMap (E.flip x) = -E.flip (f x) := by
    apply LinearMap.ext
    intro y
    exact hf y x
  have hs : Function.Surjective E.flip := (E.flip.toDual hE.flip).surjective
  rw [← contract_injective.eq_iff, map_zero, pol1_contract_exteriorDer]
  constructor
  · intro hd
    apply LinearMap.ext
    intro x
    have hh := LinearMap.congr_fun hd (E.flip x)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, he, map_neg,
      LinearMap.zero_apply] at hh
    exact sub_eq_zero.mp (show f (contract d (E.flip x)) - contract d (E.flip (f x)) = 0 from by simpa only [sub_eq_add_neg] using hh)
  · intro hc
    apply LinearMap.ext
    intro φ
    obtain ⟨x, rfl⟩ := hs φ
    have hh := LinearMap.congr_fun hc x
    change f (contract d (E.flip x)) = contract d (E.flip (f x)) at hh
    simp only [LinearMap.add_apply, LinearMap.comp_apply, he, map_neg,
      LinearMap.zero_apply, hh, add_neg_cancel]


theorem m2_formOperator_complexify {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (E : LinearMap.BilinForm ℚ V) (d : ⋀[ℚ]^2 V) :
    (m2_formOperator E d).baseChange ℂ =
      m2_formOperator (E.baseChange ℂ) (HodgeBlocks.complexifyWedge 2 d) := by
  apply ((Module.finBasis ℚ V).baseChange ℂ).ext
  intro i
  simp only [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
  have he : (E.baseChange ℂ).flip ((1 : ℂ) ⊗ₜ[ℚ] Module.finBasis ℚ V i) =
      Module.Dual.baseChange ℂ (E.flip (Module.finBasis ℚ V i)) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c x
    change E.baseChange ℂ (c ⊗ₜ[ℚ] x) ((1 : ℂ) ⊗ₜ[ℚ] Module.finBasis ℚ V i) =
      (E x (Module.finBasis ℚ V i)) • c
    rw [LinearMap.BilinForm.baseChange_tmul, mul_one]
  change (1 : ℂ) ⊗ₜ[ℚ] contract d (E.flip (Module.finBasis ℚ V i)) =
    contract (HodgeBlocks.complexifyWedge 2 d)
      ((E.baseChange ℂ).flip ((1 : ℂ) ⊗ₜ[ℚ] Module.finBasis ℚ V i))
  rw [he, pol1_contract_complexify]


theorem m2_hodge_iff_formOperator (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (E : LinearMap.BilinForm ℚ (HQ J 1)) (hE : (E.baseChange ℂ).Nondegenerate)
    (hskew : ∀ x y, E.baseChange ℂ (m2_hodgeGrading J x) y =
      -E.baseChange ℂ x (m2_hodgeGrading J y)) (d : HQ J 2) :
    d ∈ Hdg^1(J; ℚ) ↔
      m2_formOperator E (polarizationVec (torusCohomology_cupProductOf J) d) ∈ hodgeEndH1 J := by
  letI := (torusCohomology_cupProductOf J).finite
  have hclass : d ∈ Hdg^1(J; ℚ) ↔
      InvariantsExterior.exteriorDer 2 (m2_hodgeGrading J) (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) d)) = 0 := by
    refine (pol1_hodge_iff_polarizationVec_type J (finiteBetti_abelian J)
      (spec_bettiDeRhamIso_abelian J) d).trans ?_
    rw [pol1_exterior_type_iff_grading_zero,
      HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul]
    rfl
  refine hclass.trans ?_
  rw [m2_form_derivation_iff_commutes (E.baseChange ℂ) hE _ (m2_hodgeGrading J) hskew,
    ← m2_formOperator_complexify E]
  rw [eq_comm]
  exact (m2_hodgeEnd_iff_grading J _).symm


end HodgeLean.Foundations.Program

import HodgeLean.Foundations.FieldTheory.CyclicKummer
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerAction
import Mathlib.FieldTheory.Galois.Basic

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A subgroup with no extra fixed elements is the entire automorphism group. -/
theorem s2v_l1b_aut_subgroup_eq_top
    (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (H : Subgroup (E ≃ₐ[F] E))
    (hfix : IntermediateField.fixedField H = ⊥) : H = ⊤ := by
  rw [← IntermediateField.fixingSubgroup_fixedField H, hfix]
  exact IntermediateField.fixingSubgroup_bot

/-- A cyclic subgroup with the base as fixed field determines the extension degree. -/
theorem s2v_l1b_degree_of_fixed_subgroup
    (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (H : Subgroup (E ≃ₐ[F] E)) [IsCyclic H]
    (hfix : IntermediateField.fixedField H = ⊥) :
    IsGalois F E ∧ IsCyclic (E ≃ₐ[F] E) ∧ Module.finrank F E = Nat.card H := by
  have htop := s2v_l1b_aut_subgroup_eq_top F E H hfix
  haveI : IsGalois F E := IsGalois.of_fixedField_eq_bot F E (htop ▸ hfix)
  haveI : IsCyclic (E ≃ₐ[F] E) := by
    haveI : IsCyclic (⊤ : Subgroup (E ≃ₐ[F] E)) := htop ▸ inferInstance
    exact isCyclic_of_surjective (⊤ : Subgroup (E ≃ₐ[F] E)).subtype
      (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [← IntermediateField.finrank_fixedField_eq_card H, hfix]
  exact IntermediateField.finrank_bot'.symm

/-- A residual generator with the base as fixed field determines its cyclic extension degree. -/
theorem s2v_l1b_degree_of_fixed_generator
    (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (τ : E ≃ₐ[F] E)
    (hfix : IntermediateField.fixedField (Subgroup.zpowers τ) = ⊥) :
    IsGalois F E ∧ IsCyclic (E ≃ₐ[F] E) ∧ Module.finrank F E = orderOf τ := by
  exact FieldTheory.CyclicKummer.degree_of_fixed_generator F E τ hfix

/-- A degree-one change of base preserves the cyclic Galois degree in a field tower. -/
theorem s2v_l1b_cyclic_degree_tower
    (F K E : Type*) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [FiniteDimensional F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    (hbase : Module.finrank F K = 1) :
    Module.Finite K E ∧ IsGalois K E ∧ IsCyclic (E ≃ₐ[K] E) ∧
      Module.finrank K E = Module.finrank F E := by
  haveI : Module.Finite K E := Module.Finite.of_restrictScalars_finite F K E
  haveI : IsGalois K E := IsGalois.tower_top_of_isGalois F K E
  haveI : IsCyclic (E ≃ₐ[K] E) :=
    isCyclic_of_injective (AlgEquiv.restrictScalarsHom F)
      (AlgEquiv.restrictScalars_injective F)
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  have h := Module.finrank_mul_finrank F K E
  rw [hbase, one_mul] at h
  exact h

end HodgeLean.Foundations.Program

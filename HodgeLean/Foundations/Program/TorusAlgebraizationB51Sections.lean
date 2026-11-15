import HodgeLean.Foundations.Program.TorusAlgebraizationB51Basic
import HodgeLean.Foundations.AppellHumbertSections
import HodgeLean.Foundations.Program.CurveJacobianAFiniteDim

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem b5_lattice_real_basis (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    ∃ c : Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℝ (b5_V Λ F),
      Submodule.span ℤ (Set.range c) = (b5_lattice Λ F).range := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  obtain ⟨c, hc⟩ := b2_latticeMap_basis b F hF
  let e : ((ℂ ⊗[ℤ] Λ) ⧸ F) ≃ₗ[ℝ] b5_V Λ F :=
    (b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).restrictScalars ℝ
  let d : Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℝ (b5_V Λ F) := c.map e
  have hd (i : Module.Free.ChooseBasisIndex ℤ Λ) : d i = b5_lattice Λ F (b i) := by
    simp only [d, Module.Basis.map_apply, e, LinearEquiv.restrictScalars_apply, hc]
    rfl
  refine ⟨d, le_antisymm (Submodule.span_le.mpr ?_) ?_⟩
  · rintro _ ⟨i, rfl⟩
    rw [hd]
    exact LinearMap.mem_range_self _ _
  · rintro _ ⟨l, rfl⟩
    rw [← b.sum_repr l, map_sum]
    exact Submodule.sum_mem _ fun i _ ↦ by
      rw [map_zsmul, ← hd]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Restriction of theta sections to the closed parallelepiped of a real lattice basis. -/
noncomputable def b5_sectionRestriction (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (n : ℕ)
    (d : Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℝ (b5_V Λ F)) :
    b5_sections Λ F hF Q n →ₗ[ℂ] BoundedContinuousFunction d.parallelepiped ℂ := by
  letI : CompactSpace d.parallelepiped :=
    isCompact_iff_compactSpace.mp d.parallelepiped.isCompact
  exact
    { toFun := fun f ↦ BoundedContinuousFunction.mkOfCompact
        ⟨fun z ↦ f.val z, f.property.1.continuous.comp continuous_subtype_val⟩
      map_add' := fun f g ↦ by
        ext z
        rfl
      map_smul' := fun c f ↦ by
        ext z
        rfl }

end HodgeLean.Foundations.Program

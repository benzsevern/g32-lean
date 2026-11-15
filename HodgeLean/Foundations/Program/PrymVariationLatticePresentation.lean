import HodgeLean.Foundations.Program.PrymVariationLatticeSaturation

set_option maxHeartbeats 400000

noncomputable section
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

structure b63l_PeriodSaturationPresentation (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [MulAction b4b_Group C] where
  lift : b3_periodLattice ℂ C →ₗ[ℤ] b63l_periodLattice C
  surjective : Function.Surjective (lift.baseChange ℂ)
  compatible (x : ℂ ⊗[ℤ] b3_periodLattice ℂ C) :
    (b63l_periodLattice C).subtype.baseChange ℂ (lift.baseChange ℂ x) =
      (b4_groupEnd ℂ (C := C) b4b_projectorCoeff).toIntLinearMap.baseChange ℂ x
  split (w : ℂ ⊗[ℤ] b63l_periodLattice C) :
    { z : (ℂ ⊗[ℤ] b3_periodLattice ℂ C) × (ℂ ⊗[ℤ] b3_periodLattice ℂ C) //
      z.1 ∈ b3_periodF ℂ C ∧ z.2 ∈ b3_periodF ℂ C ∧
        lift.baseChange ℂ z.1 +
          lift.baseChange ℂ (b2_conj (b3_periodLattice ℂ C) z.2) = w }

opaque b63l_periodSaturationPresentation (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [MulAction b4b_Group C] :
    b63l_PeriodSaturationPresentation C := by
  let f := (b4_groupEnd ℂ (C := C) b4b_projectorCoeff).toIntLinearMap
  let L := b63l_periodLattice C
  have hbase : L.baseChange ℂ = (LinearMap.range f).baseChange ℂ := by
    apply le_antisymm
    · rw [Submodule.baseChange_eq_span]
      apply Submodule.span_le.2
      rintro z ⟨x, hx, rfl⟩
      rcases hx with ⟨n, hn, hx⟩
      change (1 ⊗ₜ[ℤ] x : ℂ ⊗[ℤ] b3_periodLattice ℂ C) ∈
        (LinearMap.range f).baseChange ℂ
      letI : TensorProduct.CompatibleSMul ℤ ℤ ℂ (b3_periodLattice ℂ C) :=
        ⟨fun m q y ↦
          (TensorProduct.CompatibleSMul.int.smul_tmul m q y).trans
            (congrArg (fun z : b3_periodLattice ℂ C ↦ q ⊗ₜ[ℤ] z)
              (Int.cast_smul_eq_zsmul ℤ m y).symm)⟩
      convert (LinearMap.range f).tmul_mem_baseChange_of_mem (n : ℂ)⁻¹ hx using 1
      rw [TensorProduct.tmul_smul]
      rw [← Int.cast_smul_eq_zsmul ℂ]
      change (1 : ℂ) ⊗ₜ[ℤ] x = ((n : ℂ) * (n : ℂ)⁻¹) ⊗ₜ[ℤ] x
      rw [mul_inv_cancel₀ (show (n : ℂ) ≠ 0 by exact_mod_cast hn)]
    · apply Submodule.baseChange_mono (A := ℂ)
      intro x hx
      exact ⟨1, one_ne_zero, (LinearMap.range f).smul_mem 1 hx⟩
  have hle : LinearMap.range f ≤ L := fun x hx ↦
    ⟨1, one_ne_zero, (LinearMap.range f).smul_mem 1 hx⟩
  let j : LinearMap.range f →ₗ[ℤ] L := Submodule.inclusion hle
  letI : Module ℤ (LinearMap.range f) := (LinearMap.range f).module
  have hj : Function.Surjective (j.baseChange ℂ) := by
    intro y
    have hy : L.subtype.baseChange ℂ y ∈ L.baseChange ℂ := ⟨y, rfl⟩
    rw [hbase] at hy
    rcases hy with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply b2a_cplxMap_subtype_injective L.toAddSubgroup
    change L.subtype.baseChange ℂ (j.baseChange ℂ z) = L.subtype.baseChange ℂ y
    rw [← hz]
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl
  let r : b3_periodLattice ℂ C →ₗ[ℤ] L :=
    { toFun := fun x ↦ ⟨f x, ⟨1, one_ne_zero,
          (LinearMap.range f).smul_mem 1 ⟨x, rfl⟩⟩⟩
      map_add' := fun x y ↦ Subtype.ext (map_add f x y)
      map_smul' := fun n x ↦ Subtype.ext (map_zsmul f n x) }
  have hr : Function.Surjective (r.baseChange ℂ) := by
    have hf : Function.Surjective (f.rangeRestrict.baseChange ℂ) :=
      LinearMap.baseChange_surjective ℂ
        (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict f))
    intro y
    rcases hj y with ⟨z, rfl⟩
    rcases hf z with ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul q x => rfl
  refine ⟨r, hr, ?_, ?_⟩
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul q x =>
        simp only [LinearMap.baseChange_tmul]
        change q ⊗ₜ[ℤ] (r x).val = q ⊗ₜ[ℤ] f x
        rfl
  · intro w
    let u := Classical.choose (hr w)
    have huw : r.baseChange ℂ u = w := Classical.choose_spec (hr w)
    have hF := b3_isWeightOne (E := ℂ) (C := C) (by norm_num)
    have hu : u ∈ b3_periodF ℂ C ⊔
        b2_conjSubmodule (b3_periodLattice ℂ C) (b3_periodF ℂ C) :=
      (codisjoint_iff_le_sup.1 hF.codisjoint) Submodule.mem_top
    let a := Classical.choose (Submodule.mem_sup.1 hu)
    have ha := (Classical.choose_spec (Submodule.mem_sup.1 hu)).1
    have hex := (Classical.choose_spec (Submodule.mem_sup.1 hu)).2
    let c := Classical.choose hex
    have hc := (Classical.choose_spec hex).1
    have hac := (Classical.choose_spec hex).2
    let c' := Classical.choose (b2a_mem_conjSubmodule.1 hc)
    have hc' := (Classical.choose_spec (b2a_mem_conjSubmodule.1 hc)).1
    have hcc' := (Classical.choose_spec (b2a_mem_conjSubmodule.1 hc)).2
    refine ⟨(a, c'), ha, hc', ?_⟩
    rw [← map_add, hcc', hac]
    exact huw

end HodgeLean.Foundations.Program

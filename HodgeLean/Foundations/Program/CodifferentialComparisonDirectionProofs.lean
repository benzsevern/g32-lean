import HodgeLean.Foundations.Program.CodifferentialComparisonChartProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonDefs


noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful


variable {c₀ : Fin 10 → ℂ} {g₀ : Fin 13 → b4b_Group}

theorem b66f_frames_in_three_space {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (F : V →ₗ[ℂ] W) (hF : Function.Injective F) (e : Fin 3 → W)
    (q q' : Fin 3 → V)
    (hq : ∀ i, F (q i) ∈ Submodule.span ℂ (Set.range e))
    (hq' : ∀ i, F (q' i) ∈ Submodule.span ℂ (Set.range e))
    (hi : LinearIndependent ℂ q) (hi' : LinearIndependent ℂ q') :
    ∃ P : Matrix (Fin 3) (Fin 3) ℂ, IsUnit P ∧
      ∀ i, q' i = ∑ a, P a i • q a := by
  let U := (Submodule.span ℂ (Set.range e)).comap F
  letI : Module.Finite ℂ (Submodule.span ℂ (Set.range e)) :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  let G : U →ₗ[ℂ] Submodule.span ℂ (Set.range e) :=
    { toFun := fun x => ⟨F x.val, x.property⟩
      map_add' := fun x y => Subtype.ext (map_add F x.val y.val)
      map_smul' := fun z x => Subtype.ext (map_smul F z x.val) }
  have hG : Function.Injective G := fun x y h => Subtype.ext (hF (congrArg Subtype.val h))
  letI : Module.Finite ℂ U := Module.Finite.of_injective G hG
  let v : Fin 3 → U := fun i => ⟨q i, hq i⟩
  let v' : Fin 3 → U := fun i => ⟨q' i, hq' i⟩
  have hv : LinearIndependent ℂ v := hi.of_comp U.subtype
  have hv' : LinearIndependent ℂ v' := hi'.of_comp U.subtype
  have hdim : Module.finrank ℂ U = 3 := by
    have hle := LinearMap.finrank_le_finrank_of_injective hG
    have hr := finrank_range_le_card (R := ℂ) e
    change Module.finrank ℂ (Submodule.span ℂ (Set.range e)) ≤ 3 at hr
    have hlo := hv.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hr hlo
    omega
  let b := Module.Basis.mk hv (hv.span_eq_top_of_card_eq_finrank (by simp [hdim])).ge
  let b' := Module.Basis.mk hv' (hv'.span_eq_top_of_card_eq_finrank (by simp [hdim])).ge
  refine ⟨b.toMatrix b', ?_, ?_⟩
  · apply isUnit_iff_exists_inv.mpr
    refine ⟨b'.toMatrix b, ?_⟩ <;>
      simp only [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
  · intro i
    simpa only [Submodule.coe_sum, Submodule.coe_smul, b, b', Module.Basis.mk_apply, Module.Basis.coe_mk, v, v'] using
      (congrArg Subtype.val (b.sum_toMatrix_smul_self b' i)).symm


def b66f_transportPeriods (R : b65z_SharedFamily c₀ g₀) (s t : b6t_polydisc c₀) :
    (ℂ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) →ₗ[ℂ] Module.Dual ℂ (b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :=
  (b3A_toDual.comp ((b3_cplxPeriod ℂ (b65z_fibre c₀ R.C t)).codRestrict
    (b3_linearDual ℂ (b65z_fibre c₀ R.C t)) (fun v => b3A_cplxPeriod_mem_linearDual v))).comp
      ((b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
        (Subset.refl _) R.P s t).baseChange ℂ)


theorem b66f_normalized_periods_complex (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (w : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) (n : ℂ ⊗[ℤ] b60_Lattice)
    (hw : ∀ x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s,
      (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
        (Subset.refl _) R.P s t x).val w =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x)) n) :
    (b66f_transportPeriods R s t).flip w =
      ((b60_E.baseChange ℂ).flip n).comp (b64b_complexMarking _ m).toLinearMap := by
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v u hv hu => simp only [map_add, hv, hu]
  | tmul c x =>
    have h1 : (b66f_transportPeriods R s t).flip w (1 ⊗ₜ[ℤ] x) =
        (((b60_E.baseChange ℂ).flip n).comp
          (b64b_complexMarking _ m).toLinearMap) (1 ⊗ₜ[ℤ] x) := by
      simpa only [b66f_transportPeriods, LinearMap.comp_apply, LinearMap.codRestrict_apply,
        b3A_toDual, LinearMap.coe_mk, AddHom.coe_mk, b3_cplxPeriod,
        LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, Pi.smul_apply,
        one_smul, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply,
        AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply, LinearEquiv.coe_coe]
        using hw x
    have hc : c ⊗ₜ[ℤ] x = c • (1 ⊗ₜ[ℤ] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc, map_smul, map_smul, h1]


end HodgeLean.Foundations.Program

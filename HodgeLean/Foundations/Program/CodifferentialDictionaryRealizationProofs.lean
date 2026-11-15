import HodgeLean.Foundations.Program.CodifferentialComparisonBasisProofs
import HodgeLean.Foundations.Program.CoverDictionaryKernels

noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

open Metric Matrix

theorem b66d_hom_eval_injective {U : Type} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ b4b_Group U) [ρ.IsIrreducible]
    (cj : Bool) (e : U ≃ₗ[ℂ] (Fin 4 → ℂ))
    (he : ∀ h u, e (ρ h u) = b65g_rep cj h (e u))
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (u : U) (hu : u ≠ 0) :
    Function.Injective (fun φ : b65g_homG D t cj => φ.val (e u)) := by
  intro φ ψ h
  let ξ : Representation.IntertwiningMap ρ (b4_formRepresentation (D.hG t)) :=
    { toLinearMap := ((φ - ψ).val.comp e.toLinearMap).codRestrict _
        (fun v => (φ - ψ).property.1 (e v))
      isIntertwining' h := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        change (φ - ψ).val (e (ρ h v)) = _
        rw [he]
        exact (φ - ψ).property.2 h (e v) }
  have hz : ξ u = 0 := Subtype.ext (sub_eq_zero.mpr h)
  rcases Representation.IsIrreducible.injective_or_eq_zero ξ with hi | hzero
  · exact False.elim (hu (hi (hz.trans (map_zero ξ).symm)))
  · apply Subtype.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    have hw := congrArg (fun f : Representation.IntertwiningMap ρ
      (b4_formRepresentation (D.hG t)) => (f w).val) hzero
    exact sub_eq_zero.mp hw

theorem b66d_eval_injective {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (cj : Bool) :
    Function.Injective (fun φ : b65g_homG D t cj => φ.val (Pi.single 0 1)) := by
  have hv : (Pi.single 0 1 : Fin 4 → ℂ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  cases cj
  · exact b66d_hom_eval_injective b63d_naturalRep false (LinearEquiv.refl ℂ _)
      (fun _ _ => rfl) D t _ hv
  · have he : ∀ h x, b65g_barEquiv (HurwitzPrymRex_barRep b63d_naturalRep h x) =
        b65g_rep true h (b65g_barEquiv x) := by
      intro h x
      funext i
      simp [b65g_barEquiv, b65g_rep, b65g_mat, HurwitzPrymRex_barRep,
        b63d_naturalRep, Matrix.mulVec, dotProduct, map_sum]
    have hu : HurwitzPrymRex_Bar.of (Pi.single 0 1 : Fin 4 → ℂ) ≠ 0 := by
      intro h
      exact hv (congrArg HurwitzPrymRex_Bar.val h)
    have h := b66d_hom_eval_injective (HurwitzPrymRex_barRep b63d_naturalRep) true
      b65g_barEquiv he D t _ hu
    have he0 : b65g_barEquiv (HurwitzPrymRex_Bar.of (Pi.single 0 1 : Fin 4 → ℂ)) =
        Pi.single 0 1 := by
      ext i
      simp [b65g_barEquiv, Pi.single_apply]
    rwa [he0] at h

theorem b66d_rep_projector (cj : Bool) :
    (∑ h : b4b_Group, (b4b_projectorCoeff h : ℂ) • b65g_rep cj h) (Pi.single 0 1) =
      (b4b_projectorDenominator : ℂ) • (Pi.single 0 1 : Fin 4 → ℂ) := by
  have hm : ∑ h : b4b_Group, (b4b_projectorCoeff h : ℂ) • b65g_mat cj h =
      (b4b_projectorDenominator : ℂ) • (Matrix.single 0 0 1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    cases cj
    · exact b63l_projector_matrix
    · ext i j
      have hh := congrArg star (congrFun (congrFun b63l_projector_matrix i) j)
      simpa [b65g_mat, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply,
        smul_eq_mul, apply_ite] using hh
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M *ᵥ (Pi.single 0 1)) hm
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  change (∑ h : b4b_Group, (b4b_projectorCoeff h : ℂ) •
    (b65g_mat cj h *ᵥ Pi.single 0 1)) = _
  simpa only [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.single_mulVec,
    Pi.single_eq_same, mul_one, Pi.single, Function.update_self, one_mul] using h

theorem b66d_chart_realization {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (cj : Bool) :
    ∃ Φ : b65g_homG D t cj →ₗ[ℂ] b66f_primitiveForms D t,
      Function.Injective Φ ∧
      ∀ φ, b66f_chartForm D t (Φ φ).val = φ.val (Pi.single 0 1) := by
  obtain ⟨M, hM, hP⟩ := b66f_gen_b66m_chart_projector hg D t
  let E : b65g_homG D t cj →ₗ[ℂ] b3_HolForm ℂ (b65z_fibre c D.C t) :=
    { toFun := fun φ => ⟨φ.val (Pi.single 0 1), φ.property.1 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let F := M.symm.toLinearMap.comp E
  have heigen (φ : b65g_homG D t cj) :
      b66f_gen_b66m_holProjector D t (E φ) =
        (b4b_projectorDenominator : ℂ) • E φ := by
    apply Subtype.ext
    have hp : b66f_gen_b66m_holProjector D t =
        ∑ h : b4b_Group, (b4b_projectorCoeff h : ℂ) • b4_formRepresentation (D.hG t) h := by
      change (∑ h : b4b_Group, (b4b_projectorCoeff h : ℂ) • b4cov_tau (D.hG t) h⁻¹) =
        ∑ h : b4b_Group, (b4b_projectorCoeff h : ℂ) • b4cov_tau (D.hG t) h
      simpa only [Equiv.inv_apply, b63l_projectorCoeff_inverse] using
        (Equiv.sum_comp (Equiv.inv b4b_Group)
          (fun h => (b4b_projectorCoeff h : ℂ) • b4cov_tau (D.hG t) h))
    rw [hp, LinearMap.sum_apply, Submodule.coe_sum]
    change (∑ h : b4b_Group, (b4b_projectorCoeff h : ℂ) •
      b4_formAct ℂ h (φ.val (Pi.single 0 1))) =
        (b4b_projectorDenominator : ℂ) • φ.val (Pi.single 0 1)
    have hh := congrArg φ.val (b66d_rep_projector cj)
    simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      φ.property.2] using hh
  have hmem (φ : b65g_homG D t cj) : (F φ).val ∈ b66f_primitiveForms D t := by
    obtain ⟨qP, hqP, hMP⟩ := hP (F φ)
    have heq : qP = (b4b_projectorDenominator : ℂ) • F φ := by
      apply M.injective
      rw [hMP, map_smul]
      change b66f_gen_b66m_holProjector D t (M (M.symm (E φ))) =
        (b4b_projectorDenominator : ℂ) • M (M.symm (E φ))
      rw [LinearEquiv.apply_symm_apply, heigen]
    have hd : (b4b_projectorDenominator : ℂ) ≠ 0 := by
      norm_num [b4b_projectorDenominator]
    refine ⟨(F φ).property, (b4b_projectorDenominator : ℂ)⁻¹ • F φ, ?_⟩
    change b66f_projector D t ((b4b_projectorDenominator : ℂ)⁻¹ • (F φ).val) = _
    rw [map_smul, ← hqP, heq]
    exact inv_smul_smul₀ hd _
  let Φ : b65g_homG D t cj →ₗ[ℂ] b66f_primitiveForms D t :=
    { toFun := fun φ => ⟨(F φ).val, hmem φ⟩
      map_add' := fun a b => Subtype.ext (congrArg (fun x : b66f_forms D t 1 => x.val) (map_add F a b))
      map_smul' := fun a b => Subtype.ext (congrArg (fun x : b66f_forms D t 1 => x.val) (map_smul F a b)) }
  have hchart (φ) : b66f_chartForm D t (Φ φ).val = φ.val (Pi.single 0 1) := by
    change b66f_chartForm D t (F φ).val = _
    rw [← hM (F φ)]
    exact congrArg Subtype.val (M.apply_symm_apply (E φ))
  refine ⟨Φ, ?_, hchart⟩
  intro φ ψ h
  apply b66d_eval_injective D t cj
  change φ.val (Pi.single 0 1) = ψ.val (Pi.single 0 1)
  rw [← hchart φ, ← hchart ψ, h]

theorem b66d_chartForm_injective {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    Function.Injective (fun q : b66f_primitiveForms D t => b66f_chartForm D t q.val) := by
  obtain ⟨M, hM⟩ := b66f_gen_b66m_chart_comparison hg D t
  intro q r h
  apply Subtype.ext
  let q' : b66f_forms D t 1 := ⟨q.val, q.property.1⟩
  let r' : b66f_forms D t 1 := ⟨r.val, r.property.1⟩
  have he : M q' = M r' := Subtype.ext ((hM q').trans (h.trans (hM r').symm))
  exact congrArg (fun x : b66f_forms D t 1 => x.val) (M.injective he)

theorem b66d_rep_scalar (cj : Bool) (v : Fin 4 → ℂ) :
    b65g_rep cj b63d_scalarElement v =
      (if cj then star g32h_omega else g32h_omega) • v := by
  cases cj
  · exact b63d_naturalRep_scalar v
  · change ((b4b_toMatrix b63d_scalarElement).map (starRingEnd ℂ)) *ᵥ v = _
    rw [b63d_scalarElement_matrix]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply, apply_ite]

theorem b66d_form_scalar {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (cj : Bool)
    (φ : b65g_homG D t cj) :
    b4_formAct ℂ b63d_scalarElement (φ.val (Pi.single 0 1)) =
      (if cj then star g32h_omega else g32h_omega) • φ.val (Pi.single 0 1) := by
  rw [← φ.property.2, b66d_rep_scalar, map_smul]

end HodgeLean.Foundations.Program

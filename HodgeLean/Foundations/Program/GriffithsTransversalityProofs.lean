import HodgeLean.Foundations.Program.GriffithsTransversalitySurjection

noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

theorem b66g_griffiths_aux (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (n : ℕ) (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) :
    ∃ E : b66g_H1O R t ≃ₗ[ℂ] ((Fin n → ℂ) ⧸ b66g_periodSubspace R s t B),
      ∀ (U : Set (Fin 10 → ℂ)) (_hU : IsOpen U) (_ht : t.val ∈ U)
      (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
      (q : b66g_forms R t 1)
      (_hq : ∀ (a : b66k_Index R) (p : rf8_fibre R.C t),
        p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
        θ.val t ⟨p, v⟩ = q.val a p.val.2 *
          (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
            (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p v)),
      DifferentiableAt ℂ (b66g_periods R s B θ) t.val ∧
      ∀ h : Fin 10 → ℂ, ∃ c : b66g_H1O R t,
        c.val = (b66g_scalarBoundaries R t).mkQ
          (b66g_contract R q.val (b66k_cocycle R t h)) ∧
        E c = (b66g_periodSubspace R s t B).mkQ
          (fderiv ℂ (b66g_periods R s B θ) t.val h) := by
  obtain ⟨P⟩ := b66g_rep_exists R s t B
  obtain ⟨hfin, hle⟩ := b66g_H1O_finrank_le (R := R) (t := t)
  have htarget := b66g_target_finrank R s t B
  set W := LinearMap.range (b66g_psi R t)
  haveI : FiniteDimensional ℂ (b66g_H1O R t) := hfin
  haveI hWfin : FiniteDimensional ℂ W := FiniteDimensional.finiteDimensional_submodule W
  have hsurj := b66g_E0_surjective P
  have hW1 : Module.finrank ℂ ((Fin n → ℂ) ⧸ b66g_periodSubspace R s t B) ≤
      Module.finrank ℂ W := by
    have := LinearMap.finrank_range_le (b66g_E0 P)
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at this
  have hW2 : Module.finrank ℂ W ≤ Module.finrank ℂ (b66g_H1O R t) := Submodule.finrank_le W
  have hWtop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  let E' : b66g_H1O R t →ₗ[ℂ] ((Fin n → ℂ) ⧸ b66g_periodSubspace R s t B) :=
    (b66g_E0 P).comp (LinearEquiv.ofTop W hWtop).symm.toLinearMap
  have hE'surj : Function.Surjective E' := by
    intro y
    obtain ⟨w, hw⟩ := hsurj y
    refine ⟨w.val, ?_⟩
    rw [← hw]
    change b66g_E0 P ((LinearEquiv.ofTop W hWtop).symm w.val) = _
    congr 1
  have hdim : Module.finrank ℂ (b66g_H1O R t) =
      Module.finrank ℂ ((Fin n → ℂ) ⧸ b66g_periodSubspace R s t B) := by omega
  have hE'inj : Function.Injective E' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hE'surj
  refine ⟨LinearEquiv.ofBijective E' ⟨hE'inj, hE'surj⟩, fun U hU ht θ q hq => ?_⟩
  obtain ⟨hdiff, hder⟩ := b66g_periods_deriv R hU ht θ q.val hq P
  refine ⟨hdiff, fun h => ?_⟩
  have hcyc := b66g_contract_mem R t q.property (b66k_cocycle_mem R t h)
  have hlift := b66g_isLift_deriv R hU ht θ q.val hq h
  let p : b66g_L R t := ⟨(b66g_contract R q.val (b66k_cocycle R t h),
    fun a w => fderiv ℂ (b66g_relCoef R θ a) (t.val, w) (h, 0)), hcyc, hlift⟩
  refine ⟨b66g_psi R t p, rfl, ?_⟩
  change b66g_E0 P ((LinearEquiv.ofTop W hWtop).symm (b66g_psi R t p)) = _
  rw [show (LinearEquiv.ofTop W hWtop).symm (b66g_psi R t p) =
    ⟨b66g_psi R t p, LinearMap.mem_range_self _ p⟩ from rfl, b66g_E0_apply, hder h]
  rfl

end HodgeLean.Foundations.Program

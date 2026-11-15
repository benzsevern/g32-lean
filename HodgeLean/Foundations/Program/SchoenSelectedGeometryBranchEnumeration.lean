import HodgeLean.Foundations.Program.SchoenSelectedGeometryBranchOrdering
import HodgeLean.Foundations.Program.SchoenSelectedGeometryBranchRepresentatives
import HodgeLean.Foundations.Program.SchoenSelectedGeometryResidualRotation

noncomputable section
set_option maxHeartbeats 400000
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful
  b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

/-- Positive residual branch generators follow the supplier's literal exponent ordering. -/
theorem s0_branch_enumeration {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j))) (S : g32p_Supplier)
    [ChartedSpace ℂ (rsq_Quot S.χ.ker (b65z_fibre c D.C t))]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker (b65z_fibre c D.C t))]
    (hq : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_proj S.χ.ker (b65z_fibre c D.C t)))
    (hA : ∀ a : S.H ⧸ S.χ.ker, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun z : rsq_Quot S.χ.ker (b65z_fibre c D.C t) ↦ a • z))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (he : ∀ h : S.H, e (QuotientGroup.mk h) = S.χ h) :
    ∃ (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker (b65z_fibre c D.C t))
      (r : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker),
      Function.Injective (fun i ↦ rsq_coarsen S.χ.ker (y i)) ∧
      (∀ i, b4_IsRotGen ℂ (y i) (r i) ∧
        e (r i) = Multiplicative.ofAdd ((g32p_exponents S)[i] : ZMod S.m)) ∧
      (∀ z, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ i, rsq_coarsen S.χ.ker z = rsq_coarsen S.χ.ker (y i)) := by
  classical
  let C := b65z_fibre c D.C t
  choose x hx hrot using D.hrot t
  let p := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Set.Subset.refl _) t
  have hfree (z : C) (hz : p z ∉ Set.range (b6_branch t.val)) :
      MulAction.stabilizer b4b_Group z = ⊥ := by
    apply g32y_stabilizer_trivial_off_branch (Module.finrank_self ℂ)
      (Module.finrank_self ℂ) (D.hG t) p (D.hk t) (D.hgal t) z
    rwa [D.hbranch t]
  have hb : Function.Injective (b6_branch t.val) :=
    (b6t_polydisc_neighbourhood c D.atlas.hb).2.2.2 t.property
  obtain ⟨hi, hc⟩ := s0_branch_representatives (D.hG t) S.H S.χ p (D.hgal t)
    (b6_branch t.val) hb x hx g hrot hfree
  obtain ⟨d, hd⟩ := s0_branch_ordering D t hg S
  let y := fun i ↦ rsq_proj S.χ.ker C (s0_branchLift S.H S.χ g x (d i))
  let r := fun i ↦ (QuotientGroup.mk
    (papersLocalMonodromy S.H (g (d i).val.1) (d i).val.2) : S.H ⧸ S.χ.ker)
  refine ⟨y, r, ?_, ?_, ?_⟩
  · exact hi.comp d.injective
  · intro i
    refine ⟨?_, ?_⟩
    · exact s0_residual_rotation (fun h : S.H ↦ D.hG t h) S.χ.ker hq hA _ _
        (g32y_papers_monodromy_rotGen (Module.finrank_self ℂ) (D.hG t) S.H _ _
          (hrot (d i).val.1) (d i).val.2)
    · dsimp only [r]
      rw [he]
      exact congrArg Multiplicative.ofAdd (hd i)
  · intro z
    induction z using Quotient.inductionOn' with
    | h z =>
      change MulAction.stabilizer (S.H ⧸ S.χ.ker) (rsq_proj S.χ.ker C z) ≠ ⊥ ↔
        ∃ i, rsq_proj S.H C z = rsq_coarsen S.χ.ker (y i)
      rw [hc z]
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨d.symm a, ?_⟩
        simpa only [y, rsq_coarsen_mk, d.apply_symm_apply] using ha
      · rintro ⟨i, hi⟩
        exact ⟨d i, hi⟩

#print axioms s0_branch_enumeration
end HodgeLean.Foundations.Program

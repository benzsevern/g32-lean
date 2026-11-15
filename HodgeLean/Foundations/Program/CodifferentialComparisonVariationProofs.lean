import HodgeLean.Foundations.Program.PathCoverFamilyAnalytic
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

theorem b66f_relative_form_frame (R : b65z_SharedFamily c₀ g₀)
    (t₀ : b6t_polydisc c₀) :
        ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ b6t_polydisc c₀ ∧
      ∃ θ : Fin (Module.finrank ℂ (b3_HolForm ℂ (b65z_fibre c₀ R.C t₀))) →
          b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) W,
        ∀ t : b6t_polydisc c₀, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _) (θ i) t) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _) (θ i) t) = ⊤ := by
  obtain ⟨D, -, -, F, -⟩ := b65z_family_plumbing R
  exact rf6_relForm_frame c₀ R.C (b6t_polydisc c₀) (Subset.refl _)
    (b6t_polydisc_neighbourhood c₀ R.atlas.hb).2.2.1
    (fun q ↦ ⟨R.atlas.A q, (R.atlas.hA q).2, (R.atlas.hA q).1, R.atlas.hparam q⟩) R.hincl F t₀

theorem b66f_relative_extension (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (φ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    ∃ (U : Set (Fin 10 → ℂ)), IsOpen U ∧ t.val ∈ U ∧ U ⊆ b6t_polydisc c₀ ∧
      ∃ θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U,
        b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _) θ t = φ := by
  obtain ⟨U, hU, ht, hsub, f, hf⟩ := b66f_relative_form_frame R t
  let E : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U →ₗ[ℂ]
      b3_HolForm ℂ (b65z_fibre c₀ R.C t) :=
    { toFun := fun θ => b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _) θ t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hspan := (hf t ht).2
  have hr : Submodule.span ℂ (Set.range fun i => E (f i)) ≤ LinearMap.range E := by
    apply Submodule.span_le.mpr
    rintro φ ⟨i, rfl⟩
    exact ⟨f i, rfl⟩
  change Submodule.span ℂ (Set.range fun i => E (f i)) = ⊤ at hspan
  rw [hspan] at hr
  obtain ⟨θ, hθ⟩ := (LinearMap.range_eq_top.mp (top_unique hr)) φ
  exact ⟨U, hU, ht, hsub, θ, hθ⟩


end HodgeLean.Foundations.Program

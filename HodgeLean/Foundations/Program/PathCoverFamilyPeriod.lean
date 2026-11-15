import HodgeLean.Foundations.Program.PathCoverFamilyAnalytic

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

theorem b65z_filtration_frame {b : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (R : b65z_SharedFamily b g)
    (s : b6t_polydisc b)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice b R.C R.hC (b6t_polydisc b) (Subset.refl _) s))
    (t₀ : b6t_polydisc b) :
        ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ b6t_polydisc b ∧
      ∃ c : Fin 6 →
          (Fin 10 → ℂ) → (Fin 12 → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t : b6t_polydisc b, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_coordVector B (c i t.val)) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_coordVector B (c i t.val)) =
            b63e_transportedF b R.C R.hC (b6t_polydisc b) (Subset.refl _) R.P s t := by
  obtain ⟨D, -, -, F, -⟩ := b65z_family_plumbing R
  obtain ⟨W, hWo, htW, hWV, c, hc, hfr⟩ := rf6_filtration_frame b R.C R.hC
    (b6t_polydisc b) (Subset.refl _)
    (b6t_polydisc_neighbourhood b R.atlas.hb).2.2.1
    (fun q ↦ ⟨R.atlas.A q, (R.atlas.hA q).2, (R.atlas.hA q).1, R.atlas.hparam q⟩) R.hincl R.hG R.Q R.hQ R.P R.hP F s B t₀
  have hrank := b65z_transported_finrank hg R s t₀
  let e : Fin 6 ≃ Fin (Module.finrank ℂ (b63e_transportedF b R.C R.hC
      (b6t_polydisc b) (Subset.refl _) R.P s t₀)) := finCongr hrank.symm
  refine ⟨W, hWo, htW, hWV, fun i ↦ c (e i), fun i ↦ hc (e i), fun t ht ↦ ?_⟩
  obtain ⟨hli, hsp⟩ := hfr t ht
  refine ⟨hli.comp e e.injective, ?_⟩
  rw [← hsp]
  congr 1
  exact e.surjective.range_comp (fun i ↦ b63e_coordVector B (c i t.val))

theorem b65z_period_analytic {b : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (R : b65z_SharedFamily b g)
    (s : b6t_polydisc b)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice b R.C R.hC (b6t_polydisc b)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ b R.C R.hC (b6t_polydisc b) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y) :
    AnalyticOnNhd ℂ (b65z_period R s m) (b6t_polydisc b) := by
  obtain ⟨B⟩ := b65z_lattice_basis hg R s
  have hchart := b65z_period_chart hg R s m hJ hpol
  apply b64c_period_analyticOnNhd _ B m (b6t_polydisc b) (b65z_polydisc_open b)
    (b65z_transportedFamily R s) ?_ (fun t ht ↦ ⟨_, ((hchart t ht).2).symm⟩)
  intro t₀ ht₀
  obtain ⟨W, hWo, htW, hWV, c, hc, hspan⟩ :=
    b65z_filtration_frame hg R s B ⟨t₀, ht₀⟩
  refine ⟨W, hWo, htW, hWV, 6, c, hc, ?_⟩
  intro t ht
  simpa only [b65z_transportedFamily, dite_eq_left (hWV ht)] using
    (hspan ⟨t, hWV ht⟩ ht).2

end HodgeLean.Foundations.Program

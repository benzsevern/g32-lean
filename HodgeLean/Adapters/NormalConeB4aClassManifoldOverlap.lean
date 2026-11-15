import HodgeLean.Adapters.NormalConeB4aClassManifoldInverse
import HodgeLean.Adapters.NormalConeB4aClassChartFinrank
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionOverlap

/-! # Normal-coclass agreement for analytic manifold charts

Route: inverse regularity makes chart transitions analytic in both directions.
Their complex dimensions agree. Apply the complex normal orientation
comparison to obtain exact coclass agreement on a common neighborhood.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology TopologicalSpace AlgebraicTopology.Singular
open scoped Manifold ContDiff

/-- Two analytic manifold charts flattening the same support in normal
codimension `c` have equal normal coclasses on a small common neighborhood. -/
theorem a3b4a_classManifoldChart_normalCoclass_overlap
    {D M : Type} [NormedAddCommGroup D] [NormedSpace ℂ D] [FiniteDimensional ℂ D]
    [TopologicalSpace M] [ChartedSpace D M] [IsManifold 𝓘(ℂ, D) ω M]
    {r s c : ℕ} (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin c → ℂ)))
    (e' : OpenPartialHomeomorph M ((Fin s → ℂ) × (Fin c → ℂ)))
    (he : ContMDiffOn 𝓘(ℂ, D) 𝓘(ℂ, (Fin r → ℂ) × (Fin c → ℂ)) ω e e.source)
    (he' : ContMDiffOn 𝓘(ℂ, D) 𝓘(ℂ, (Fin s → ℂ) × (Fin c → ℂ)) ω e' e'.source)
    (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hS' : ∀ y ∈ e'.source, y ∈ S ↔ (e' y).2 = 0)
    (x : M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) (hxS : x ∈ S) :
    ∃ (W : Opens M) (hW : (W : Set M) ⊆ e.source) (hW' : (W : Set M) ⊆ e'.source),
      x ∈ W ∧ chartNormalProjectionCoclass (Fin r → ℂ) c e S hS W hW =
        chartNormalProjectionCoclass (Fin s → ℂ) c e' S hS' W hW' := by
  have hei := a3b4a_classManifoldChart_inverse e he
  let t := e.symm.trans e'
  have ht : AnalyticOnNhd ℂ t t.source := by
    intro z hz
    have h₁ := (hei z hz.1).contMDiffAt (e.open_target.mem_nhds hz.1)
    have h₂ := (he' (e.symm z) hz.2).contMDiffAt (e'.open_source.mem_nhds hz.2)
    exact (h₂.comp z h₁).contDiffAt.analyticAt
  have hxT : e x ∈ t.source := ⟨e.map_source hx, by
    change e.symm (e x) ∈ e'.source
    rwa [e.left_inv hx]⟩
  have hdim := a3b4a_classAnalyticChart_finrank t ht ⟨e x, hxT⟩
  simp only [Module.finrank_prod, Module.finrank_fin_fun] at hdim
  have hrs : r = s := Nat.add_right_cancel hdim
  subst s
  exact exists_open_chartNormalProjectionCoclass_eq c e e' S hS hS' x hx
    ((hS x hx).mp hxS) hx' (ht _ hxT)
    (a3b4a_classAnalyticInverse_finiteDimensional t ht _ (t.map_source hxT))

end HodgeLean.Adapters

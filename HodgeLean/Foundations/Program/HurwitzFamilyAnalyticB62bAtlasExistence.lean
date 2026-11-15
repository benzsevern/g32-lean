import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bConstruction

noncomputable section

open scoped Manifold ContDiff
open Manifold

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6a_analytic_atlas_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (U : Type) [TopologicalSpace U]
    [MulAction G U] [ConnectedSpace U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G)
    (C₀ : Type) [TopologicalSpace C₀] [ChartedSpace ℂ C₀]
    [IsManifold 𝓘(ℂ, ℂ) ω C₀] [T2Space C₀] [CompactSpace C₀]
    [ConnectedSpace C₀] [MulAction G C₀] (f₀ : C₀ → OnePoint ℂ) (ι₀ : U → C₀)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f₀)
    (hgal : b4_IsGaloisCover G f₀) (hsurj : Function.Surjective f₀)
    (hact : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C₀ ↦ g • x))
    (hι : Topology.IsOpenEmbedding ι₀)
    (hrange : Set.range ι₀ = f₀ ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hproj : ∀ u, f₀ (ι₀ u) = π u)
    (hequiv : ∀ (g : G) (u : U), ι₀ (g • u) = g • ι₀ u)
    (n₀ : C₀ → ℕ) (hn : ∀ x, 0 < n₀ x)
    (hunram : ∀ x, f₀ x ∉ Set.range (b6_branch b) → n₀ x = 1)
    (hlocal : ∀ x (j : Fin 13), f₀ x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C₀ ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C₀ ∧ P x = 0 ∧
        (∀ y ∈ P.source, f₀ y = b6a_value b j (P y ^ n₀ x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n₀ x = 1 ∧
          Set.MapsTo (fun y : C₀ ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction G C) (f : C → OnePoint ℂ) (ι : U → C),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ b4_IsGaloisCover G f ∧
      Function.Surjective f ∧
      (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
      Topology.IsOpenEmbedding ι ∧
      Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ ∧
      (∀ u, f (ι u) = π u) ∧
      (∀ (g : G) (u : U), ι (g • u) = g • ι u) ∧
      ∃ (_ : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
        (_ : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C))
        (A : (b6t_polydisc b × C) →
          OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
        (n : C → ℕ),
        (∀ x, 0 < n x) ∧
        (∀ q, q ∈ (A q).source ∧ A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)) ∧
        (∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val) ∧
        (∀ q, f q.2 ∉ Set.range (b6_branch b) → n q.2 = 1 ∧
          ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ)) ∧
        (∀ q (j : Fin 13), f q.2 = b6_branch b j →
          (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
            b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2)) := by
  letI : Nonempty U := b6a_cover_nonempty b G U π hπ
  let A := b6a_isolatedFamilyChart b hb G U C₀ π hπ f₀ ι₀ hι hrange n₀ hn hlocal hf.continuous
  have hA : ∀ q, q ∈ (A q).source :=
    b6a_mem_isolatedFamilyChart_source b hb G U C₀ π hπ f₀ ι₀ hι hrange n₀ hn hlocal hf.continuous
  let cs := b6a_familyChartedSpace b C₀ A hA
  letI : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C₀) := cs
  have hman : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C₀) :=
    b6a_isolatedFamilyChart_isManifold b hb G U C₀ π hπ f₀ ι₀ hι hrange n₀ hn hlocal hf.continuous hproj
  have hformula := b6a_isolatedFamilyChart_formulas b hb G U C₀ π hπ f₀ ι₀ hι
    hrange n₀ hn hlocal hf.continuous hproj
  refine ⟨C₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, f₀, ι₀, hf, hgal, hsurj, hact, hι, hrange, hproj, hequiv,
    cs, hman, A, n₀, hn, (fun q ↦ ⟨hA q, ⟨q, rfl⟩⟩), hformula.1, ?_, hformula.2.2⟩
  intro q hq
  exact ⟨hunram q.2 hq, hformula.2.1 q hq⟩


#print axioms b6a_analytic_atlas_aux

end HodgeLean.Foundations.Program


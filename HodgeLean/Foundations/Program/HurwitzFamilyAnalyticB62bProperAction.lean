import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bAction
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bTopology

noncomputable section
open Manifold
open scoped Manifold ContDiff

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6a_family_proper_action_aux (b : Fin 10 → ℂ) (G C : Type)
    [Group G] [TopologicalSpace C] [CompactSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (hb : b ∈ b6_chart) [Finite G] (U : Type)
    [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [ConnectedSpace C] (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f) (hsurj : Function.Surjective f)
    (hact : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : G) (u : U), ι (g • u) = g • ι u)
    (n : C → ℕ) (hn : ∀ x, 0 < n x)
    (hunram : ∀ x, f x ∉ Set.range (b6_branch b) → n x = 1)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2)) :
    IsProperMap (fun q : b6t_polydisc b × C ↦ q.1) ∧
      ∀ g : G, ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
        (fun q : b6t_polydisc b × C ↦ (q.1, g • q.2)) := by
  refine ⟨b6a_projection_proper b C, ?_⟩
  intro g
  apply b6a_lift_contMDiff b C f n hn A hA hparam hfree hmark
    (fun q ↦ (q.1, g • q.2))
  · exact continuous_fst.prodMk ((hact g).continuous.comp continuous_snd)
  · intro y
    rfl
  · intro y
    exact hgal.1 g y.2

#print axioms b6a_family_proper_action_aux

end HodgeLean.Foundations.Program

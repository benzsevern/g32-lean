import HodgeLean.Foundations.Program.HurwitzFamilyMarkedProofs

/-! # B4 refinement: retain the prescribed based monodromy

Implication from a surjective based monodromy homomorphism to a compact filling
with its original punctured covering and marked lift point. This refines the
existence interface; it does not identify independent conjugacy-data selections.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Manifold CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- A compact B4 filling retaining the entire prescribed based monodromy homomorphism.
Source: Forster, *Lectures on Riemann Surfaces*, §§5, 8, Theorem 8.4;
Hatcher, *Algebraic Topology*, Theorem 1.38 and Proposition 1.40. -/
theorem b6m_marked_rex (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (x₀ : b6t_punctured b)
    (φ : FundamentalGroup (b6t_punctured b) x₀ →* Gᵐᵒᵖ)
    (hφ : Function.Surjective φ) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : MulAction G U)
      (_ : ConnectedSpace U) (π : U → b6t_punctured b)
      (hπ : IsQuotientCoveringMap π G) (u₀ : π ⁻¹' {x₀}),
      hπ.fundamentalGroupToMulOpposite u₀ = φ ∧
      ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
        (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
        (_ : ConnectedSpace C) (_ : MulAction G C) (f : C → OnePoint ℂ) (ι : U → C),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ b4_IsGaloisCover G f ∧
        Function.Surjective f ∧
        (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
        Topology.IsOpenEmbedding ι ∧ Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ ∧
        (∀ u, f (ι u) = π u) ∧ (∀ (g : G) (u : U), ι (g • u) = g • ι u) :=
  b6m_marked_rex_aux b hb G x₀ φ hφ

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (x₀ : b6t_punctured b)
    (φ : FundamentalGroup (b6t_punctured b) x₀ →* Gᵐᵒᵖ)
    (hφ : Function.Surjective φ) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : MulAction G U)
      (_ : ConnectedSpace U) (π : U → b6t_punctured b)
      (hπ : IsQuotientCoveringMap π G) (u₀ : π ⁻¹' {x₀}),
      hπ.fundamentalGroupToMulOpposite u₀ = φ ∧
      ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
        (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
        (_ : ConnectedSpace C) (_ : MulAction G C) (f : C → OnePoint ℂ) (ι : U → C),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ b4_IsGaloisCover G f ∧
        Function.Surjective f ∧
        (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
        Topology.IsOpenEmbedding ι ∧ Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ ∧
        (∀ u, f (ι u) = π u) ∧ (∀ (g : G) (u : U), ι (g • u) = g • ι u) :=
  b6m_marked_rex b hb G x₀ φ hφ

end HodgeLean.Foundations.Program

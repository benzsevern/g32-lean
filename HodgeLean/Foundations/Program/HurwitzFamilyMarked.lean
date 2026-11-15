import HodgeLean.Foundations.Program.HurwitzPrymMarked

/-! # B6-2c: marked identification and integral homology transport

Implication from a supplied holomorphic filling of the transported punctured
cover to a marked B4 comparison; implication from the fixed product topology
to integral transport, and from holomorphic sphere projections to preservation
of B3 intersection pairings. Holomorphic Prym variation and period coordinates
are later work. HC no distance; AV milestone no distance.
-/

noncomputable section
open Manifold CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Two compact holomorphic fillings of the same punctured cover have a unique marked comparison.
Source: Forster, *Lectures on Riemann Surfaces*, Theorem 8.4, uniqueness of filling;
Harris–Morrison, *Moduli of Curves*, §1.G. -/
theorem b6m_filling_unique (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (U : Type) [TopologicalSpace U]
    [MulAction G U] [ConnectedSpace U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D] [MulAction G C] [MulAction G D]
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ) (ι : U → C) (j : U → D)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hι : Topology.IsOpenEmbedding ι) (hj : Topology.IsOpenEmbedding j)
    (hrι : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hrj : Set.range j = k ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hpι : ∀ u, f (ι u) = π u) (hpj : ∀ u, k (j u) = π u)
    (heι : ∀ (g : G) (u : U), ι (g • u) = g • ι u)
    (hej : ∀ (g : G) (u : U), j (g • u) = g • j u)
    (haC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (haD : ∀ g : G, Continuous (fun x : D ↦ g • x)) :
    ∃ e : C ≃ₜ D,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm ∧
      (∀ u, e (ι u) = j u) ∧ (∀ x, k (e x) = f x) ∧
      (∀ (g : G) (x : C), e (g • x) = g • e x) ∧
      ∀ e' : C ≃ₜ D, (∀ u, e' (ι u) = j u) → e' = e :=
  b6m_filling_unique_aux b hb G U π hπ C D f k ι j hf hk hι hj hrι hrj hpι hpj heι hej haC haD

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (U : Type) [TopologicalSpace U]
    [MulAction G U] [ConnectedSpace U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D] [MulAction G C] [MulAction G D]
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ) (ι : U → C) (j : U → D)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hι : Topology.IsOpenEmbedding ι) (hj : Topology.IsOpenEmbedding j)
    (hrι : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hrj : Set.range j = k ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hpι : ∀ u, f (ι u) = π u) (hpj : ∀ u, k (j u) = π u)
    (heι : ∀ (g : G) (u : U), ι (g • u) = g • ι u)
    (hej : ∀ (g : G) (u : U), j (g • u) = g • j u)
    (haC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (haD : ∀ g : G, Continuous (fun x : D ↦ g • x)) :
    ∃ e : C ≃ₜ D,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm ∧
      (∀ u, e (ι u) = j u) ∧ (∀ x, k (e x) = f x) ∧
      (∀ (g : G) (x : C), e (g • x) = g • e x) ∧
      ∀ e' : C ≃ₜ D, (∀ u, e' (ι u) = j u) → e' = e :=
  b6m_filling_unique b hb G U π hπ C D f k ι j hf hk hι hj hrι hrj hpι hpj heι hej haC haD

/-- The analytic fibre is identified with a B4 filling of its exact transported marked cover.
Source: Fulton, Ann. Math. 90 (1969), 542–575; Harris–Morrison, §1.G;
Forster, Theorem 8.4; G32 v0.16, §5 (intended application). -/
theorem b6m_fibre_marking (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b)
    (G : Type) [Group G] [Finite G] (U : Type) [TopologicalSpace U]
    [MulAction G U] [ConnectedSpace U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G) (x₀ : b6t_punctured b) (u₀ : π ⁻¹' {x₀})
    (hx₀ : (x₀ : OnePoint ℂ) ∉ ⋃ i : Fin 10,
      ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (b i) (b6t_radius b))
    (γ : Fin 13 → FundamentalGroup (b6t_punctured b) x₀)
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [MulAction G C] (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (ha : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (hι : Topology.IsOpenEmbedding ι)
    (hr : Set.range ι = f ⁻¹' (Set.range (b6_branch t))ᶜ)
    (hp : ∀ u, f (ι u) = b6t_projection b t π u)
    (he : ∀ (g : G) (u : U), ι (g • u) = g • ι u) :
    b4_IsGaloisCover G f ∧ Function.Surjective f ∧
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x) ∧
      (e x₀ : OnePoint ℂ) = x₀ ∧
      ((hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
        ⟨u₀.val, congrArg e u₀.property⟩).comp
        (FundamentalGroup.map ⟨e, e.continuous⟩ x₀) =
        hπ.fundamentalGroupToMulOpposite u₀ ∧
      (∀ i, (hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
        ⟨u₀.val, congrArg e u₀.property⟩
        (FundamentalGroup.map ⟨e, e.continuous⟩ x₀ (γ i)) =
          hπ.fundamentalGroupToMulOpposite u₀ (γ i)) ∧
      ∃ (D : Type) (_ : TopologicalSpace D) (_ : ChartedSpace ℂ D)
        (_ : IsManifold 𝓘(ℂ, ℂ) ω D) (_ : T2Space D) (_ : CompactSpace D)
        (_ : ConnectedSpace D) (_ : MulAction G D) (k : D → OnePoint ℂ) (j : U → D),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k ∧ b4_IsGaloisCover G k ∧
        Function.Surjective k ∧
        (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : D ↦ g • x)) ∧
        Topology.IsOpenEmbedding j ∧ Set.range j = k ⁻¹' (Set.range (b6_branch t))ᶜ ∧
        (∀ u, k (j u) = e (π u)) ∧ (∀ (g : G) (u : U), j (g • u) = g • j u) ∧
        ∃ E : C ≃ₜ D, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω E ∧
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω E.symm ∧
          (∀ u, E (ι u) = j u) ∧ (∀ x, k (E x) = f x) ∧
          (∀ (g : G) (x : C), E (g • x) = g • E x) :=
  b6m_fibre_marking_aux b hb t ht G U π hπ x₀ u₀ hx₀ γ C f ι hf ha hι hr hp he

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b)
    (G : Type) [Group G] [Finite G] (U : Type) [TopologicalSpace U]
    [MulAction G U] [ConnectedSpace U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G) (x₀ : b6t_punctured b) (u₀ : π ⁻¹' {x₀})
    (hx₀ : (x₀ : OnePoint ℂ) ∉ ⋃ i : Fin 10,
      ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (b i) (b6t_radius b))
    (γ : Fin 13 → FundamentalGroup (b6t_punctured b) x₀)
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [MulAction G C] (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (ha : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (hι : Topology.IsOpenEmbedding ι)
    (hr : Set.range ι = f ⁻¹' (Set.range (b6_branch t))ᶜ)
    (hp : ∀ u, f (ι u) = b6t_projection b t π u)
    (he : ∀ (g : G) (u : U), ι (g • u) = g • ι u) :
    b4_IsGaloisCover G f ∧ Function.Surjective f ∧
    ∃ e : b6t_punctured b ≃ₜ b6t_punctured t,
      (∀ x, (e x : OnePoint ℂ) = b6t_sphere b t x) ∧
      (e x₀ : OnePoint ℂ) = x₀ ∧
      ((hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
        ⟨u₀.val, congrArg e u₀.property⟩).comp
        (FundamentalGroup.map ⟨e, e.continuous⟩ x₀) =
        hπ.fundamentalGroupToMulOpposite u₀ ∧
      (∀ i, (hπ.homeomorph_comp e).fundamentalGroupToMulOpposite
        ⟨u₀.val, congrArg e u₀.property⟩
        (FundamentalGroup.map ⟨e, e.continuous⟩ x₀ (γ i)) =
          hπ.fundamentalGroupToMulOpposite u₀ (γ i)) ∧
      ∃ (D : Type) (_ : TopologicalSpace D) (_ : ChartedSpace ℂ D)
        (_ : IsManifold 𝓘(ℂ, ℂ) ω D) (_ : T2Space D) (_ : CompactSpace D)
        (_ : ConnectedSpace D) (_ : MulAction G D) (k : D → OnePoint ℂ) (j : U → D),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k ∧ b4_IsGaloisCover G k ∧
        Function.Surjective k ∧
        (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : D ↦ g • x)) ∧
        Topology.IsOpenEmbedding j ∧ Set.range j = k ⁻¹' (Set.range (b6_branch t))ᶜ ∧
        (∀ u, k (j u) = e (π u)) ∧ (∀ (g : G) (u : U), j (g • u) = g • j u) ∧
        ∃ E : C ≃ₜ D, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω E ∧
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω E.symm ∧
          (∀ u, E (ι u) = j u) ∧ (∀ x, k (E x) = f x) ∧
          (∀ (g : G) (x : C), E (g • x) = g • E x) :=
  b6m_fibre_marking b hb t ht G U π hπ x₀ u₀ hx₀ γ C f ι hf ha hι hr hp he

/-- Equal based monodromy identifies separately constructed marked compact fillings.
Source: Hatcher, *Algebraic Topology*, Theorem 1.38 and Proposition 1.40;
Forster, *Lectures on Riemann Surfaces*, Theorem 8.4; Harris–Morrison, §1.G. -/
theorem b6m_based_filling_comparison (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (U W : Type)
    [TopologicalSpace U] [TopologicalSpace W] [MulAction G U] [MulAction G W]
    [ConnectedSpace U] [ConnectedSpace W]
    (π : U → b6t_punctured b) (ρ : W → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G) (hρ : IsQuotientCoveringMap ρ G)
    (x₀ : b6t_punctured b) (u₀ : π ⁻¹' {x₀}) (w₀ : ρ ⁻¹' {x₀})
    (hmono : hπ.fundamentalGroupToMulOpposite u₀ = hρ.fundamentalGroupToMulOpposite w₀)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D] [MulAction G C] [MulAction G D]
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ) (ι : U → C) (j : W → D)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hι : Topology.IsOpenEmbedding ι) (hj : Topology.IsOpenEmbedding j)
    (hrι : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hrj : Set.range j = k ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hpι : ∀ u, f (ι u) = π u) (hpj : ∀ w, k (j w) = ρ w)
    (heι : ∀ (g : G) (u : U), ι (g • u) = g • ι u)
    (hej : ∀ (g : G) (w : W), j (g • w) = g • j w)
    (haC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (haD : ∀ g : G, Continuous (fun x : D ↦ g • x)) :
    ∃ a : U ≃ₜ W, a u₀.val = w₀.val ∧
      (∀ u, ρ (a u) = π u) ∧ (∀ (g : G) (u : U), a (g • u) = g • a u) ∧
      ∃ e : C ≃ₜ D,
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm ∧
        (∀ u, e (ι u) = j (a u)) ∧ (∀ x, k (e x) = f x) ∧
        (∀ (g : G) (x : C), e (g • x) = g • e x) ∧
        e (ι u₀.val) = j w₀.val ∧
        ∀ e' : C ≃ₜ D, (∀ x, k (e' x) = f x) →
          e' (ι u₀.val) = j w₀.val → e' = e :=
  b6m_based_filling_comparison_aux b hb G U W π ρ hπ hρ x₀ u₀ w₀ hmono C D f k ι j hf hk hι hj hrι hrj hpι hpj heι hej haC haD

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (U W : Type)
    [TopologicalSpace U] [TopologicalSpace W] [MulAction G U] [MulAction G W]
    [ConnectedSpace U] [ConnectedSpace W]
    (π : U → b6t_punctured b) (ρ : W → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G) (hρ : IsQuotientCoveringMap ρ G)
    (x₀ : b6t_punctured b) (u₀ : π ⁻¹' {x₀}) (w₀ : ρ ⁻¹' {x₀})
    (hmono : hπ.fundamentalGroupToMulOpposite u₀ = hρ.fundamentalGroupToMulOpposite w₀)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D] [MulAction G C] [MulAction G D]
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ) (ι : U → C) (j : W → D)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hι : Topology.IsOpenEmbedding ι) (hj : Topology.IsOpenEmbedding j)
    (hrι : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hrj : Set.range j = k ⁻¹' (Set.range (b6_branch b))ᶜ)
    (hpι : ∀ u, f (ι u) = π u) (hpj : ∀ w, k (j w) = ρ w)
    (heι : ∀ (g : G) (u : U), ι (g • u) = g • ι u)
    (hej : ∀ (g : G) (w : W), j (g • w) = g • j w)
    (haC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (haD : ∀ g : G, Continuous (fun x : D ↦ g • x)) :
    ∃ a : U ≃ₜ W, a u₀.val = w₀.val ∧
      (∀ u, ρ (a u) = π u) ∧ (∀ (g : G) (u : U), a (g • u) = g • a u) ∧
      ∃ e : C ≃ₜ D,
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm ∧
        (∀ u, e (ι u) = j (a u)) ∧ (∀ x, k (e x) = f x) ∧
        (∀ (g : G) (x : C), e (g • x) = g • e x) ∧
        e (ι u₀.val) = j w₀.val ∧
        ∀ e' : C ≃ₜ D, (∀ x, k (e' x) = f x) →
          e' (ι u₀.val) = j w₀.val → e' = e :=
  b6m_based_filling_comparison b hb G U W π ρ hπ hρ x₀ u₀ w₀ hmono C D f k ι j hf hk hι hj hrι hrj hpι hpj heι hej haC haD

/-- Transport extends over every filled point and its integral map is induced by that homeomorphism.
Source: Harris–Morrison, *Moduli of Curves*, §1.G; Hatcher, §2.1;
G32 v0.16, §5, marking the moving covers. -/
theorem b6m_filled_transport (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (f : C → OnePoint ℂ)
    (U : Type) (π : U → b6t_punctured b) (ι : U → C)
    (hp : ∀ u, f (ι u) = π u)
    (s t : b6t_polydisc b) :
    (∀ u, b6m_transport b C s t ⟨(s, ι u), rfl⟩ = ⟨(t, ι u), rfl⟩) ∧
    (∀ u, b6a_map b f (b6m_transport b C s t ⟨(s, ι u), rfl⟩).val =
      b6t_projection b t.val π u) ∧
    (∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ,
      (∀ z, e z = b6t_sphere b t.val z) ∧
      ∀ x : b6m_Fibre b C ⟨b, (b6t_polydisc_neighbourhood b hb).1⟩,
        b6a_map b f (b6m_transport b C ⟨b, (b6t_polydisc_neighbourhood b hb).1⟩ t x).val =
          e (b6a_map b f x.val)) ∧
    (b6m_H1Equiv (b6m_transport b C s t)).toLinearMap =
      homologyMap ℤ 1 (TopCat.ofHom
        ⟨b6m_transport b C s t, (b6m_transport b C s t).continuous⟩) :=
  b6m_filled_transport_aux b hb C f U π ι hp s t

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (f : C → OnePoint ℂ)
    (U : Type) (π : U → b6t_punctured b) (ι : U → C)
    (hp : ∀ u, f (ι u) = π u)
    (s t : b6t_polydisc b) :
    (∀ u, b6m_transport b C s t ⟨(s, ι u), rfl⟩ = ⟨(t, ι u), rfl⟩) ∧
    (∀ u, b6a_map b f (b6m_transport b C s t ⟨(s, ι u), rfl⟩).val =
      b6t_projection b t.val π u) ∧
    (∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ,
      (∀ z, e z = b6t_sphere b t.val z) ∧
      ∀ x : b6m_Fibre b C ⟨b, (b6t_polydisc_neighbourhood b hb).1⟩,
        b6a_map b f (b6m_transport b C ⟨b, (b6t_polydisc_neighbourhood b hb).1⟩ t x).val =
          e (b6a_map b f x.val)) ∧
    (b6m_H1Equiv (b6m_transport b C s t)).toLinearMap =
      homologyMap ℤ 1 (TopCat.ofHom
        ⟨b6m_transport b C s t, (b6m_transport b C s t).continuous⟩) :=
  b6m_filled_transport b hb C f U π ι hp s t

/-- Integral homology transport intertwines the actual induced deck transformations.
Source: Hatcher, *Algebraic Topology*, §2.1, functoriality; G32 v0.16, §5. -/
theorem b6m_homology_equivariant (b : Fin 10 → ℂ) (G C : Type) [Group G]
    [TopologicalSpace C] [MulAction G C]
    (hC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (s t : b6t_polydisc b) (g : G) (x : b6m_H1 (b6m_Fibre b C s)) :
    (∀ q : b6m_Fibre b C s,
      b6m_transport b C s t (b6m_deck b G C hC s g q) =
        b6m_deck b G C hC t g (b6m_transport b C s t q)) ∧
    b6m_H1Equiv (b6m_transport b C s t)
      (homologyMap ℤ 1 (TopCat.ofHom (b6m_deck b G C hC s g)) x) =
      homologyMap ℤ 1 (TopCat.ofHom (b6m_deck b G C hC t g))
        (b6m_H1Equiv (b6m_transport b C s t) x) :=
  b6m_homology_equivariant_aux b G C hC s t g x

example (b : Fin 10 → ℂ) (G C : Type) [Group G]
    [TopologicalSpace C] [MulAction G C]
    (hC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (s t : b6t_polydisc b) (g : G) (x : b6m_H1 (b6m_Fibre b C s)) :
    (∀ q : b6m_Fibre b C s,
      b6m_transport b C s t (b6m_deck b G C hC s g q) =
        b6m_deck b G C hC t g (b6m_transport b C s t q)) ∧
    b6m_H1Equiv (b6m_transport b C s t)
      (homologyMap ℤ 1 (TopCat.ofHom (b6m_deck b G C hC s g)) x) =
      homologyMap ℤ 1 (TopCat.ofHom (b6m_deck b G C hC t g))
        (b6m_H1Equiv (b6m_transport b C s t) x) :=
  b6m_homology_equivariant b G C hC s t g x

/-- The product coordinates trivialize integral homology transport and give its cocycle identity.
Source: Fulton, Ann. Math. 90 (1969), 542–575; Harris–Morrison, §1.G;
Hatcher, §2.1, functoriality. -/
theorem b6m_homology_trivialization (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (s : b6t_polydisc b) :
    (∀ t : b6t_polydisc b,
      ((b6m_H1Equiv (b6m_coordinate b C s)).symm.trans
        (b6m_H1Equiv (b6m_transport b C s t))).trans
        (b6m_H1Equiv (b6m_coordinate b C t)) = LinearEquiv.refl ℤ (b6m_H1 C)) ∧
    IsLocallyConstant (fun t : b6t_polydisc b ↦
      ((b6m_H1Equiv (b6m_coordinate b C s)).symm.trans
        (b6m_H1Equiv (b6m_transport b C s t))).trans
        (b6m_H1Equiv (b6m_coordinate b C t))) ∧
    (∀ t u : b6t_polydisc b,
      (b6m_H1Equiv (b6m_transport b C s t)).trans
        (b6m_H1Equiv (b6m_transport b C t u)) =
          b6m_H1Equiv (b6m_transport b C s u)) ∧
    ∃ η : b6m_integralLocalSystem b C ≅
        (Functor.const (FundamentalGroupoid (b6t_polydisc b))).obj (b6m_H1 C),
      ∀ t : b6t_polydisc b, (η.hom.app (.mk t)).hom =
        (b6m_H1Equiv (b6m_coordinate b C t)).toLinearMap :=
  b6m_homology_trivialization_aux b C s

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (s : b6t_polydisc b) :
    (∀ t : b6t_polydisc b,
      ((b6m_H1Equiv (b6m_coordinate b C s)).symm.trans
        (b6m_H1Equiv (b6m_transport b C s t))).trans
        (b6m_H1Equiv (b6m_coordinate b C t)) = LinearEquiv.refl ℤ (b6m_H1 C)) ∧
    IsLocallyConstant (fun t : b6t_polydisc b ↦
      ((b6m_H1Equiv (b6m_coordinate b C s)).symm.trans
        (b6m_H1Equiv (b6m_transport b C s t))).trans
        (b6m_H1Equiv (b6m_coordinate b C t))) ∧
    (∀ t u : b6t_polydisc b,
      (b6m_H1Equiv (b6m_transport b C s t)).trans
        (b6m_H1Equiv (b6m_transport b C t u)) =
          b6m_H1Equiv (b6m_transport b C s u)) ∧
    ∃ η : b6m_integralLocalSystem b C ≅
        (Functor.const (FundamentalGroupoid (b6t_polydisc b))).obj (b6m_H1 C),
      ∀ t : b6t_polydisc b, (η.hom.app (.mk t)).hom =
        (b6m_H1Equiv (b6m_coordinate b C t)).toLinearMap :=
  b6m_homology_trivialization b C s

/-- The integral singular lattice is identified with B3 periods on actual smooth loop classes.
Source: Farkas–Kra, *Riemann Surfaces*, 2nd ed., Ch. III, period lattice and homology;
Hatcher, *Algebraic Topology*, §2.A, degree-one Hurewicz theorem. -/
theorem b6m_period_comparison (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    ∃ P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C,
      ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ :=
  b6m_period_comparison_aux C

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    ∃ P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C,
      ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ :=
  b6m_period_comparison C

/-- Filled transport preserves the B3 pairing under the integral period comparisons.
Source: Farkas–Kra, *Riemann Surfaces*, Ch. III, oriented intersection pairing;
Harris–Morrison, §1.G; G32 v0.16, §5. The radial sphere isotopy preserves orientation. -/
theorem b6m_intersection_transport (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (hs : Function.Surjective f)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R) :
    ∃ (P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C)
      (S : b6m_H1 D ≃ₗ[ℤ] b3_periodLattice ℂ D),
      (∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) ∧
      (∀ γ : b3_SmoothLoop ℂ D, S (b6m_loopClass D γ) = b3_latticePeriod ℂ D γ) ∧
      ∀ x y : b6m_H1 C,
        R (S (b6m_H1Equiv e x)) (S (b6m_H1Equiv e y)) = Q (P x) (P y) :=
  b6m_intersection_transport_aux b hb t ht C D f k hf hk hs e he Q hQ R hR

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (hs : Function.Surjective f)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R) :
    ∃ (P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C)
      (S : b6m_H1 D ≃ₗ[ℤ] b3_periodLattice ℂ D),
      (∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) ∧
      (∀ γ : b3_SmoothLoop ℂ D, S (b6m_loopClass D γ) = b3_latticePeriod ℂ D γ) ∧
      ∀ x y : b6m_H1 C,
        R (S (b6m_H1Equiv e x)) (S (b6m_H1Equiv e y)) = Q (P x) (P y) :=
  b6m_intersection_transport b hb t ht C D f k hf hk hs e he Q hQ R hR

end HodgeLean.Foundations.Program

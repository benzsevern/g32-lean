import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticProofs

/-! # B6-2b: moving branched covers and their analytic total space

Implication from a finite-group quotient covering of a punctured normalized sphere
to a filled, marked local analytic family. Comparison with independently selected
B4 fibres and homology transport belong to B6-2c.
HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped Manifold ContDiff
open Manifold

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The moving power model is holomorphic jointly in all parameters and the root coordinate.
Source: Fulton, Ann. Math. 90 (1969), 542–575, local Hurwitz construction; polynomial calculus. -/
theorem b6a_power_holomorphic (i : Fin 10) (e : ℕ) :
    ContDiff ℂ ω (b6a_power i e) :=
  b6a_power_holomorphic_aux i e

example (i : Fin 10) (e : ℕ) :
    ContDiff ℂ ω (b6a_power i e) :=
  b6a_power_holomorphic i e

/-- The local ramification locus excludes exponent one.
Source: Harris–Morrison, *Moduli of Curves*, §1.G, power-map local model; polynomial derivative. -/
theorem b6a_power_derivative (i : Fin 10) (e : ℕ) (he : 0 < e) (t : Fin 10 → ℂ) (w : ℂ) :
    HasDerivAt (fun z : ℂ ↦ (b6a_power i e (t, z)).2) ((e : ℂ) * w ^ (e - 1)) w ∧
      (((e : ℂ) * w ^ (e - 1) = 0) ↔ 1 < e ∧ w = 0) :=
  b6a_power_derivative_aux i e he t w

example (i : Fin 10) (e : ℕ) (he : 0 < e) (t : Fin 10 → ℂ) (w : ℂ) :
    HasDerivAt (fun z : ℂ ↦ (b6a_power i e (t, z)).2) ((e : ℂ) * w ^ (e - 1)) w ∧
      (((e : ℂ) * w ^ (e - 1) = 0) ↔ 1 < e ∧ w = 0) :=
  b6a_power_derivative i e he t w

/-- A continuous nonzero root of a holomorphic transition function is holomorphic.
Source: complex inverse function theorem for the power map; Harris–Morrison,
*Moduli of Curves*, §1.G, gluing local covers. -/
theorem b6a_root_transition (s : Set ((Fin 10 → ℂ) × ℂ)) (hs : IsOpen s)
    (h r : ((Fin 10 → ℂ) × ℂ) → ℂ) (hh : ContDiffOn ℂ ω h s)
    (hr : ContinuousOn r s) (e : ℕ) (he : 0 < e)
    (hne : ∀ q ∈ s, r q ≠ 0) (hpow : ∀ q ∈ s, r q ^ e = h q) :
    ContDiffOn ℂ ω r s :=
  b6a_root_transition_aux s hs h r hh hr e he hne hpow

example (s : Set ((Fin 10 → ℂ) × ℂ)) (hs : IsOpen s)
    (h r : ((Fin 10 → ℂ) × ℂ) → ℂ) (hh : ContDiffOn ℂ ω h s)
    (hr : ContinuousOn r s) (e : ℕ) (he : 0 < e)
    (hne : ∀ q ∈ s, r q ≠ 0) (hpow : ∀ q ∈ s, r q ^ e = h q) :
    ContDiffOn ℂ ω r s :=
  b6a_root_transition s hs h r hh hr e he hne hpow

/-- Every transported punctured cover has an equivariant compact holomorphic filling.
Source: `b4_extend_galoisCovering`, Forster, *Lectures on Riemann Surfaces*, Theorem 8.4;
`b6t_cover`. -/
theorem b6a_fill_transport (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (U : Type) [TopologicalSpace U]
    [MulAction G U] [ConnectedSpace U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction G C) (f : C → OnePoint ℂ) (ι : U → C),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ b4_IsGaloisCover G f ∧
      Function.Surjective f ∧
      (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
      Topology.IsOpenEmbedding ι ∧
      Set.range ι = f ⁻¹' (Set.range (b6_branch t))ᶜ ∧
      (∀ u, f (ι u) = b6t_projection b t π u) ∧
      (∀ (g : G) (u : U), ι (g • u) = g • ι u) :=
  b6a_fill_transport_aux b hb G U π hπ t ht

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G : Type) [Group G] [Finite G] (U : Type) [TopologicalSpace U]
    [MulAction G U] [ConnectedSpace U] (π : U → b6t_punctured b)
    (hπ : IsQuotientCoveringMap π G)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction G C) (f : C → OnePoint ℂ) (ι : U → C),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f ∧ b4_IsGaloisCover G f ∧
      Function.Surjective f ∧
      (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
      Topology.IsOpenEmbedding ι ∧
      Set.range ι = f ⁻¹' (Set.range (b6_branch t))ᶜ ∧
      (∀ u, f (ι u) = b6t_projection b t π u) ∧
      (∀ (g : G) (u : U), ι (g • u) = g • ι u) :=
  b6a_fill_transport b hb G U π hπ t ht

/-- A common analytic atlas has parameter coordinates and the stated local power formulas.
Source: Fulton, Ann. Math. 90 (1969), 542–575; Harris–Morrison, *Moduli of Curves*, §1.G. -/
theorem b6a_analytic_atlas (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
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
  exact b6a_analytic_atlas_aux b hb G U π hπ
    C₀ f₀ ι₀ hf hgal hsurj hact hι hrange hproj hequiv n₀ hn hunram hlocal

example (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
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
  exact b6a_analytic_atlas b hb G U π hπ
    C₀ f₀ ι₀ hf hgal hsurj hact hι hrange hproj hequiv n₀ hn hunram hlocal

/-- The common total-space charts have holomorphic transition maps.
Source: complex inverse function theorem; Harris–Morrison, *Moduli of Curves*, §1.G. -/
theorem b6a_chart_compatibility (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hb : b ∈ b6_chart) (G U : Type) [Group G] [Finite G]
    [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    (f : C → OnePoint ℂ) (ι : U → C)
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
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2)) :
    ∀ q q', ContDiffOn ℂ ω ((A q).symm.trans (A q'))
      ((A q).symm.trans (A q')).source := by
  exact b6a_chart_compatibility_aux b C A hA
    hb G U π hπ f ι hf hgal hsurj hact hι hrange hproj hequiv n hn hunram hlocal hparam hfree hmark

example (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hb : b ∈ b6_chart) (G U : Type) [Group G] [Finite G]
    [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    (f : C → OnePoint ℂ) (ι : U → C)
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
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2)) :
    ∀ q q', ContDiffOn ℂ ω ((A q).symm.trans (A q'))
      ((A q).symm.trans (A q')).source := by
  exact b6a_chart_compatibility b C A hA
    hb G U π hπ f ι hf hgal hsurj hact hι hrange hproj hequiv n hn hunram hlocal hparam hfree hmark

/-- The total sphere map is holomorphic in the common analytic structure.
Source: Fulton, Ann. Math. 90 (1969), 542–575, local Hurwitz construction. -/
theorem b6a_total_map_holomorphic (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] [ChartedSpace ℂ C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (f : C → OnePoint ℂ)
    (hb : b ∈ b6_chart) (G U : Type) [Group G] [Finite G]
    [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [MulAction G C] (ι : U → C)
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
    ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω (b6a_map b f) := by
  exact b6a_total_map_holomorphic_aux b C f
    hb G U π hπ ι hf hgal hsurj hact hι hrange hproj hequiv n hn hunram hlocal A hA hparam hfree hmark

example (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C] [ChartedSpace ℂ C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (f : C → OnePoint ℂ)
    (hb : b ∈ b6_chart) (G U : Type) [Group G] [Finite G]
    [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [MulAction G C] (ι : U → C)
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
    ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω (b6a_map b f) := by
  exact b6a_total_map_holomorphic b C f
    hb G U π hπ ι hf hgal hsurj hact hι hrange hproj hequiv n hn hunram hlocal A hA hparam hfree hmark

/-- The parameter projection is holomorphic and a submersion.
Source: the parameter-coordinate identity in the common analytic atlas. -/
theorem b6a_family_projection (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (hb : b ∈ b6_chart) (G U : Type) [Group G] [Finite G]
    [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    (f : C → OnePoint ℂ) (ι : U → C)
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
    ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, Fin 10 → ℂ) ω
        (fun q : b6t_polydisc b × C ↦ q.1.val) ∧
      IsSubmersion 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, Fin 10 → ℂ) ω
        (fun q : b6t_polydisc b × C ↦ q.1.val) := by
  exact b6a_family_projection_aux b C
    hb G U π hπ f ι hf hgal hsurj hact hι hrange hproj hequiv n hn hunram hlocal A hA hparam hfree hmark

example (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (hb : b ∈ b6_chart) (G U : Type) [Group G] [Finite G]
    [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    (f : C → OnePoint ℂ) (ι : U → C)
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
    ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, Fin 10 → ℂ) ω
        (fun q : b6t_polydisc b × C ↦ q.1.val) ∧
      IsSubmersion 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, Fin 10 → ℂ) ω
        (fun q : b6t_polydisc b × C ↦ q.1.val) := by
  exact b6a_family_projection b C
    hb G U π hπ f ι hf hgal hsurj hact hι hrange hproj hequiv n hn hunram hlocal A hA hparam hfree hmark

/-- The family projection is proper and the total group action is holomorphic.
Source: compactness of the filled surface and equivariant power charts. -/
theorem b6a_family_proper_action (b : Fin 10 → ℂ) (G C : Type)
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
  exact b6a_family_proper_action_aux b G C
    hb U π hπ f ι hf hgal hsurj hact hι hrange hproj hequiv n hn hunram hlocal A hA hparam hfree hmark

example (b : Fin 10 → ℂ) (G C : Type)
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
  exact b6a_family_proper_action b G C
    hb U π hπ f ι hf hgal hsurj hact hι hrange hproj hequiv n hn hunram hlocal A hA hparam hfree hmark

/-- Each fibre has its transported holomorphic Galois-cover geometry.
Source: Forster, *Lectures on Riemann Surfaces*, Theorem 8.4, and the common atlas. -/
theorem b6a_fibre_geometry (b : Fin 10 → ℂ) (G U C : Type)
    [Group G] [TopologicalSpace U] [MulAction G U] [TopologicalSpace C]
    [MulAction G C] (π : U → b6t_punctured b) (f : C → OnePoint ℂ) (ι : U → C)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (hb : b ∈ b6_chart) [Finite G] [ConnectedSpace U]
    (hπ : IsQuotientCoveringMap π G)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
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
    ∀ t : b6t_polydisc b,
          ∃ (_ : ChartedSpace ℂ C) (_ : IsManifold 𝓘(ℂ, ℂ) ω C),
            ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ b6a_map b f (t, x)) ∧
            ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (fun x : C ↦ (t, x)) ∧
            b4_IsGaloisCover G (fun x : C ↦ b6a_map b f (t, x)) ∧
            Function.Surjective (fun x : C ↦ b6a_map b f (t, x)) ∧
            (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
            Set.range ι = (fun x : C ↦ b6a_map b f (t, x)) ⁻¹'
              (Set.range (b6_branch t.val))ᶜ ∧
            (∀ u, b6a_map b f (t, ι u) = b6t_projection b t.val π u) := by
  exact b6a_fibre_geometry_aux b G U C π f ι
    hb hπ hf hgal hsurj hact hι hrange hproj hequiv n hn hunram hlocal A hA hparam hfree hmark

example (b : Fin 10 → ℂ) (G U C : Type)
    [Group G] [TopologicalSpace U] [MulAction G U] [TopologicalSpace C]
    [MulAction G C] (π : U → b6t_punctured b) (f : C → OnePoint ℂ) (ι : U → C)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (hb : b ∈ b6_chart) [Finite G] [ConnectedSpace U]
    (hπ : IsQuotientCoveringMap π G)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
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
    ∀ t : b6t_polydisc b,
          ∃ (_ : ChartedSpace ℂ C) (_ : IsManifold 𝓘(ℂ, ℂ) ω C),
            ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ b6a_map b f (t, x)) ∧
            ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (fun x : C ↦ (t, x)) ∧
            b4_IsGaloisCover G (fun x : C ↦ b6a_map b f (t, x)) ∧
            Function.Surjective (fun x : C ↦ b6a_map b f (t, x)) ∧
            (∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) ∧
            Set.range ι = (fun x : C ↦ b6a_map b f (t, x)) ⁻¹'
              (Set.range (b6_branch t.val))ᶜ ∧
            (∀ u, b6a_map b f (t, ι u) = b6t_projection b t.val π u) := by
  exact b6a_fibre_geometry b G U C π f ι
    hb hπ hf hgal hsurj hact hι hrange hproj hequiv n hn hunram hlocal A hA hparam hfree hmark

end HodgeLean.Foundations.Program

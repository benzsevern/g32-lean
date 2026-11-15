import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian16Proofs

/-! # Compatible cones and support vanishing

Implications from geometric sphere filling to compatible chains, and from a
codimension-two cover to support vanishing. Analytic singular restriction is a
frozen endpoint awaiting critical-cover integration. General nonnested
restriction requires additional local-support work.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology TopologicalSpace CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

/-- Choose one path from the fixed vertex to every singular vertex.
Source: Hatcher, Algebraic Topology, §2.1; `bh14_simplex_extension` at dimension zero. -/
theorem bh16_vertex_cones (n : ℕ) (U : Opens (Fin n → ℂ))
    (p : U)
    (hfill : ∀ (k : ℕ), k ≤ 2 →
      ∀ u : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn u (Metric.sphere 0 1) →
        MapsTo u (Metric.sphere 0 1) (U : Set (Fin n → ℂ)) →
        ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
          ContinuousOn v (Metric.closedBall 0 1) ∧
          MapsTo v (Metric.closedBall 0 1) (U : Set (Fin n → ℂ)) ∧
          ∀ z ∈ Metric.sphere 0 1, v z = u z) :
    ∃ s₀ : bh16_simplex (TopCat.of U) 0 → bh16_simplex (TopCat.of U) 1, ∀ σ,
      bh16_face (TopCat.of U) 0 0 (s₀ σ) = σ ∧
      bh16_face (TopCat.of U) 0 1 (s₀ σ) = bh16_const (TopCat.of U) 0 p :=
  bh16_vertex_cones_aux n U p hfill

/-- Extend the already chosen vertex paths over each triangular boundary.
Source: Hatcher, Algebraic Topology, §2.1; `bh14_simplex_extension` at dimension one. -/
theorem bh16_edge_cones (n : ℕ) (U : Opens (Fin n → ℂ))
    (p : U)
    (hfill : ∀ (k : ℕ), k ≤ 2 →
      ∀ u : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn u (Metric.sphere 0 1) →
        MapsTo u (Metric.sphere 0 1) (U : Set (Fin n → ℂ)) →
        ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
          ContinuousOn v (Metric.closedBall 0 1) ∧
          MapsTo v (Metric.closedBall 0 1) (U : Set (Fin n → ℂ)) ∧
          ∀ z ∈ Metric.sphere 0 1, v z = u z)
    (s₀ : bh16_simplex (TopCat.of U) 0 → bh16_simplex (TopCat.of U) 1) (h₀ : ∀ σ, bh16_face (TopCat.of U) 0 0 (s₀ σ) = σ ∧
      bh16_face (TopCat.of U) 0 1 (s₀ σ) = bh16_const (TopCat.of U) 0 p) :
    ∃ s₁ : bh16_simplex (TopCat.of U) 1 → bh16_simplex (TopCat.of U) 2, ∀ σ,
      bh16_face (TopCat.of U) 1 0 (s₁ σ) = σ ∧
      ∀ i : Fin 2, bh16_face (TopCat.of U) 1 i.succ (s₁ σ) = s₀ (bh16_face (TopCat.of U) 0 i (σ)) :=
  bh16_edge_cones_aux n U p hfill s₀ h₀

/-- Extend the compatible edge cones over each tetrahedral boundary.
Source: Hatcher, Algebraic Topology, §2.1; `bh14_simplex_extension` at dimension two. -/
theorem bh16_triangle_cones (n : ℕ) (U : Opens (Fin n → ℂ))
    (p : U)
    (hfill : ∀ (k : ℕ), k ≤ 2 →
      ∀ u : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn u (Metric.sphere 0 1) →
        MapsTo u (Metric.sphere 0 1) (U : Set (Fin n → ℂ)) →
        ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
          ContinuousOn v (Metric.closedBall 0 1) ∧
          MapsTo v (Metric.closedBall 0 1) (U : Set (Fin n → ℂ)) ∧
          ∀ z ∈ Metric.sphere 0 1, v z = u z)
    (s₀ : bh16_simplex (TopCat.of U) 0 → bh16_simplex (TopCat.of U) 1) (h₀ : ∀ σ, bh16_face (TopCat.of U) 0 0 (s₀ σ) = σ ∧
      bh16_face (TopCat.of U) 0 1 (s₀ σ) = bh16_const (TopCat.of U) 0 p)
    (s₁ : bh16_simplex (TopCat.of U) 1 → bh16_simplex (TopCat.of U) 2) (h₁ : ∀ σ, bh16_face (TopCat.of U) 1 0 (s₁ σ) = σ ∧
      ∀ i : Fin 2, bh16_face (TopCat.of U) 1 i.succ (s₁ σ) = s₀ (bh16_face (TopCat.of U) 0 i (σ))) :
    ∃ s₂ : bh16_simplex (TopCat.of U) 2 → bh16_simplex (TopCat.of U) 3, ∀ σ,
      bh16_face (TopCat.of U) 2 0 (s₂ σ) = σ ∧
      ∀ i : Fin 3, bh16_face (TopCat.of U) 2 i.succ (s₂ σ) = s₁ (bh16_face (TopCat.of U) 1 i (σ)) :=
  bh16_triangle_cones_aux n U p hfill s₀ h₀ s₁ h₁

/-- Linear extension of coherent simplex cones satisfies the chain homotopy identity.
Source: Hatcher, Algebraic Topology, §2.1 and §2.A; `SSet.ιChainComplex_d`. -/
theorem bh16_cone_identity (n : ℕ) (U : Opens (Fin n → ℂ))
    (p : U) (s₀ : bh16_simplex (TopCat.of U) 0 → bh16_simplex (TopCat.of U) 1) (h₀ : ∀ σ, bh16_face (TopCat.of U) 0 0 (s₀ σ) = σ ∧
      bh16_face (TopCat.of U) 0 1 (s₀ σ) = bh16_const (TopCat.of U) 0 p) (s₁ : bh16_simplex (TopCat.of U) 1 → bh16_simplex (TopCat.of U) 2) (h₁ : ∀ σ, bh16_face (TopCat.of U) 1 0 (s₁ σ) = σ ∧
      ∀ i : Fin 2, bh16_face (TopCat.of U) 1 i.succ (s₁ σ) = s₀ (bh16_face (TopCat.of U) 0 i (σ))) (s₂ : bh16_simplex (TopCat.of U) 2 → bh16_simplex (TopCat.of U) 3) (h₂ : ∀ σ, bh16_face (TopCat.of U) 2 0 (s₂ σ) = σ ∧
      ∀ i : Fin 3, bh16_face (TopCat.of U) 2 i.succ (s₂ σ) = s₁ (bh16_face (TopCat.of U) 1 i (σ))) :
    (∀ c : (SingularChainComplex ℚ (TopCat.of U)).X 0, ((SingularChainComplex ℚ (TopCat.of U)).d 1 0).hom (bh16_linearCone (TopCat.of U) 0 s₀ c) +
      bh16_generator (TopCat.of U) 0 (bh16_const (TopCat.of U) 0 p) (bh16_augmentation (TopCat.of U) c) = c) ∧
    (∀ c : (SingularChainComplex ℚ (TopCat.of U)).X 1,
      ((SingularChainComplex ℚ (TopCat.of U)).d 2 1).hom (bh16_linearCone (TopCat.of U) 1 s₁ c) +
        bh16_linearCone (TopCat.of U) 0 s₀ (((SingularChainComplex ℚ (TopCat.of U)).d 1 0).hom c) = c) ∧
    (∀ c : (SingularChainComplex ℚ (TopCat.of U)).X 2,
      ((SingularChainComplex ℚ (TopCat.of U)).d 3 2).hom (bh16_linearCone (TopCat.of U) 2 s₂ c) +
        bh16_linearCone (TopCat.of U) 1 s₁ (((SingularChainComplex ℚ (TopCat.of U)).d 2 1).hom c) = c) :=
  bh16_cone_identity_aux n U p s₀ h₀ s₁ h₁ s₂ h₂

/-- The two chain identities kill positive homology and hence its rational dual.
Source: Hatcher, Algebraic Topology, §2.A and §3.1; `cohomologyEquivDualHomology`. -/
theorem bh16_cone_cohomology (n : ℕ) (U : Opens (Fin n → ℂ))
    (s₀ : (SingularChainComplex ℚ (TopCat.of U)).X 0 →ₗ[ℚ] (SingularChainComplex ℚ (TopCat.of U)).X 1) (s₁ : (SingularChainComplex ℚ (TopCat.of U)).X 1 →ₗ[ℚ] (SingularChainComplex ℚ (TopCat.of U)).X 2) (s₂ : (SingularChainComplex ℚ (TopCat.of U)).X 2 →ₗ[ℚ] (SingularChainComplex ℚ (TopCat.of U)).X 3)
    (h₁ : ∀ c : (SingularChainComplex ℚ (TopCat.of U)).X 1,
      ((SingularChainComplex ℚ (TopCat.of U)).d 2 1).hom (s₁ c) + s₀ (((SingularChainComplex ℚ (TopCat.of U)).d 1 0).hom c) = c)
    (h₂ : ∀ c : (SingularChainComplex ℚ (TopCat.of U)).X 2,
      ((SingularChainComplex ℚ (TopCat.of U)).d 3 2).hom (s₂ c) + s₁ (((SingularChainComplex ℚ (TopCat.of U)).d 2 1).hom c) = c) (j : ℕ) (hj : 0 < j ∧ j ≤ 2) :
    Subsingleton (Cohomology ℚ (TopCat.of U) j) :=
  bh16_cone_cohomology_aux n U s₀ s₁ s₂ h₁ h₂ j hj

/-- Sphere fillings imply rational cohomology vanishing in degrees one and two.
Source: the compatible cone construction and Hatcher, Algebraic Topology, §2.A and §3.1. -/
theorem bh16_filling_cohomology (n : ℕ) (U : Opens (Fin n → ℂ))
    (hne : (U : Set (Fin n → ℂ)).Nonempty)
    (hfill : ∀ (k : ℕ), k ≤ 2 →
      ∀ u : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn u (Metric.sphere 0 1) →
        MapsTo u (Metric.sphere 0 1) (U : Set (Fin n → ℂ)) →
        ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
          ContinuousOn v (Metric.closedBall 0 1) ∧
          MapsTo v (Metric.closedBall 0 1) (U : Set (Fin n → ℂ)) ∧
          ∀ z ∈ Metric.sphere 0 1, v z = u z) (j : ℕ) (hj : 0 < j ∧ j ≤ 2) :
    Subsingleton (Cohomology ℚ (TopCat.of U) j) :=
  bh16_filling_cohomology_aux n U hne hfill j hj

/-- The cover has a nonempty path-connected complement.
Source: `bh14_small_translation` and `bh14_cover_sphere_filling` at dimension zero. -/
theorem bh16_cover_connected (n : ℕ) (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ))
    (hU : ∀ j, IsOpen (U j))
    (hg : ∀ j, DifferentiableOn ℂ (g j) (U j))
    (hd : ∀ j, (U j).Nonempty → d j + 2 ≤ n)
    (hcover : Oᶜ = ⋃ j, g j '' U j) :
    PathConnectedSpace O :=
  bh16_cover_connected_aux n O hO d U g hU hg hd hcover

/-- Contractibility and the low-degree absolute calculation give relative vanishing.
Source: Hatcher, Algebraic Topology, §3.1; `relativeDualCochainShortComplexInt_shortExact`. -/
theorem bh16_pair_vanishing (n : ℕ) (O : Set (Fin n → ℂ))
    (hc : PathConnectedSpace O)
    (hv : ∀ j : ℕ, 0 < j ∧ j ≤ 2 → Subsingleton (Cohomology ℚ (TopCat.of O) j))
    (k : ℕ) (hk : k ≤ 3) :
    Subsingleton (RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O) k) :=
  bh16_pair_vanishing_aux n O hc hv k hk

/-- Codimension-two covers imply support vanishing through degree three.
Source: Hatcher, Algebraic Topology, §3.1; the compatible cone and pair sequence. -/
theorem bh16_cover_support_vanishing (n : ℕ) (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ))
    (hU : ∀ j, IsOpen (U j))
    (hg : ∀ j, DifferentiableOn ℂ (g j) (U j))
    (hd : ∀ j, (U j).Nonempty → d j + 2 ≤ n)
    (hcover : Oᶜ = ⋃ j, g j '' U j) (k : ℕ) (hk : k ≤ 3) :
    Subsingleton (RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O) k) :=
  bh16_cover_support_vanishing_aux n O hO d U g hU hg hd hcover k hk

/-- For nested subspaces the triple sequence gives restriction injectivity.
Source: Hatcher, Algebraic Topology, §3.1 (the triple long exact sequence). -/
theorem bh16_nested_restriction (n : ℕ) (O Z : Set (Fin n → ℂ))
    (hsub : Zᶜ ⊆ O)
    (hv : Subsingleton (RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O) 2)) :
    Function.Injective
      (relativeCohomologyMap ℚ 2
        (TopPair.ofSubsetHom
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
          (fun _ h ↦ h) :
          TopPair.ofSubset (X := TopCat.of O) {p | p.1 ∉ Z} ⟶
          TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) Zᶜ)) :=
  bh16_nested_restriction_aux n O Z hsub hv

/-- Codimension-two removal inside the support preserves degree-two supported classes.
Source: Hatcher, Algebraic Topology, §3.1; support vanishing and the nested triple. -/
theorem bh16_cover_nested_restriction (n : ℕ) (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ))
    (hU : ∀ j, IsOpen (U j))
    (hg : ∀ j, DifferentiableOn ℂ (g j) (U j))
    (hd : ∀ j, (U j).Nonempty → d j + 2 ≤ n)
    (hcover : Oᶜ = ⋃ j, g j '' U j) (Z : Set (Fin n → ℂ)) (hsub : Zᶜ ⊆ O) :
    Function.Injective
      (relativeCohomologyMap ℚ 2
        (TopPair.ofSubsetHom
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
          (fun _ h ↦ h) :
          TopPair.ofSubset (X := TopCat.of O) {p | p.1 ∉ Z} ⟶
          TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) Zᶜ)) :=
  bh16_cover_nested_restriction_aux n O hO d U g hU hg hd hcover Z hsub

/-- Removing the critical zeros of a reduced analytic equation preserves degree-two classes.
Source: Hatcher, Algebraic Topology, §3.1; Gunning--Rossi, Analytic Functions of Several Complex Variables, Chapter III. -/
theorem bh16_singular_restriction (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p)) :
    Function.Injective (relativeCohomologyMap ℚ 2 (bh8_regularInclusion n f)) :=
  bh16_singular_restriction_aux n f hf hred

end HodgeLean.Adapters

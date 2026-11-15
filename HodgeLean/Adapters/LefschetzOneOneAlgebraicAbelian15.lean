import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian15Proofs
/-! # Codimension-two analytic cover primitives

Implications from reduced analytic equations and from local biholomorphisms.
These interfaces separate immersion charts, the second dimension drop, and
countable assembly. The Boundary modules supply the algebraic coheight transfer.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
open HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

/-- A regular hypersurface has an anchored chart with injective derivative.
Source: Gunning–Rossi, Chapter I.B; the graph and left inverse in
`astrat_regular_parametrization_aux`. -/
theorem bh15_regular_immersion_chart (n : ℕ)
    (W : Set (Fin (n + 1) → ℂ)) (hW : IsOpen W)
    (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f W)
    (z : Fin (n + 1) → ℂ) (hz : z ∈ W) (hzero : f z = 0)
    (hreg : fderiv ℂ f z ≠ 0) :
    ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin (n + 1) → ℂ))
      (g : (Fin n → ℂ) → (Fin (n + 1) → ℂ)),
      IsOpen U ∧ (0 : Fin n → ℂ) ∈ U ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      AnalyticOnNhd ℂ g U ∧ (∀ t ∈ U, Function.Injective (fderiv ℂ g t)) ∧
      g 0 = z ∧ g '' U = V ∩ {x | f x = 0} :=
  bh15_regular_immersion_chart_aux n W hW f hf z hz hzero hreg

/-- A proper equation has a countable covering by immersed hypersurface charts.
The images can contain points outside the zero set.
Source: `astrat_finite_derivative`, `bh15_regular_immersion_chart`, and the
countable extraction in `astrat_zero_set_cover_aux`. -/
theorem bh15_zero_set_immersion_cover (n : ℕ)
    (W : Set (Fin (n + 1) → ℂ)) (hW : IsOpen W) (hc : IsPreconnected W)
    (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f W)
    (a : Fin (n + 1) → ℂ) (ha : a ∈ W) (hne : f a ≠ 0) :
    ∃ (U : ℕ → Set (Fin n → ℂ))
      (g : ℕ → (Fin n → ℂ) → (Fin (n + 1) → ℂ)),
      (∀ j, IsOpen (U j)) ∧ (∀ j, AnalyticOnNhd ℂ (g j) (U j)) ∧
      (∀ j t, t ∈ U j → Function.Injective (fderiv ℂ (g j) t)) ∧
      (∀ j, MapsTo (g j) (U j) W) ∧
      W ∩ {x | f x = 0} ⊆ ⋃ j, g j '' U j :=
  bh15_zero_set_immersion_cover_aux n W hW hc f hf a ha hne

/-- An immersed hypersurface contains the germ of a regular irreducible hypersurface at each parameter anchor.
Source: the holomorphic inverse function theorem applied to an injective derivative minor;
Gunning–Rossi, Chapter I.B and II.B. -/
theorem bh15_immersion_hypersurface_germ (n : ℕ) (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (g : (Fin n → ℂ) → (Fin (n + 1) → ℂ)) (t : Fin n → ℂ)
    (ht : t ∈ U) (hg : AnalyticAt ℂ g t)
    (hi : Function.Injective (fderiv ℂ g t)) :
    ∃ q : (Fin (n + 1) → ℂ) → ℂ,
      AnalyticAt ℂ q (g t) ∧ IsIrreducibleAt q (g t) ∧
      fderiv ℂ q (g t) ≠ 0 ∧
      ∀ᶠ p in 𝓝 (g t), q p = 0 → p ∈ g '' U :=
  bh15_immersion_hypersurface_germ_aux n U hU g t ht hg hi

/-- The critical zeros of a reduced equation have empty interior in an immersed hypersurface.
Source: `bh12_no_critical_hypersurface`, `bh15_immersion_hypersurface_germ`,
and Gunning–Rossi, Chapter I.B. -/
theorem bh15_critical_pullback_interior (n : ℕ) (f : (Fin (n + 1) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (n + 1) p))
    (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (g : (Fin n → ℂ) → (Fin (n + 1) → ℂ)) (hg : AnalyticOnNhd ℂ g U)
    (hi : ∀ t ∈ U, Function.Injective (fderiv ℂ g t)) :
    interior (U ∩ g ⁻¹' {p | f p = 0 ∧ fderiv ℂ f p = 0}) = ∅ :=
  bh15_critical_pullback_interior_aux n f hf hred U hU g hg hi

/-- Local analytic equations and empty interior give strictly smaller nonempty charts.
The guard also covers ambient dimension zero.
Source: `astrat_local_parametrization` and removal of empty full-dimensional charts. -/
theorem bh15_thin_local_cover (n : ℕ) (Z : Set (Fin n → ℂ))
    (hZ : ∀ z ∈ Z, ∃ (V : Set (Fin n → ℂ)), IsOpen V ∧ z ∈ V ∧
      ∃ (r : ℕ) (F : Fin r → (Fin n → ℂ) → ℂ),
        (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
        ∀ x ∈ V, (x ∈ Z ↔ ∀ i, F i x = 0))
    (hi : interior Z = ∅) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, (U j).Nonempty → d j < n) ∧ (∀ j, IsOpen (U j)) ∧
      (∀ j, AnalyticOnNhd ℂ (g j) (U j)) ∧ Z = ⋃ j, g j '' U j :=
  bh15_thin_local_cover_aux n Z hZ hi

/-- Reduced entire equations have countable critical-zero covers of codimension at least two.
Source: `bh15_zero_set_immersion_cover`, `bh15_critical_pullback_interior`,
`astrat_pullback_equations`, and `bh15_thin_local_cover`. -/
theorem bh15_critical_stratification (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p)) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, (U j).Nonempty → d j + 2 ≤ n) ∧
      (∀ j, IsOpen (U j)) ∧ (∀ j, DifferentiableOn ℂ (g j) (U j)) ∧
      {p | f p = 0 ∧ fderiv ℂ f p = 0} = ⋃ j, g j '' U j :=
  bh15_critical_stratification_aux n f hf hred

/-- A locally biholomorphic map pulls back a countable holomorphic cover without increasing parameter dimensions.
Source: local inverse composition and second countability of complex affine space;
`spec_complexExponential_localBiholomorph` supplies the intended local inverses. -/
theorem bh15_lift_cover (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (Fin n → ℂ) M] (F : (Fin n → ℂ) → M)
    (hloc : ∀ p, ∃ e : OpenPartialHomeomorph (Fin n → ℂ) M,
      p ∈ e.source ∧ EqOn F e e.source ∧
      ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω e.symm e.target)
    (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → M)
    (hU : ∀ j, IsOpen (U j))
    (hg : ∀ j, ContMDiffOn 𝓘(ℂ, Fin (d j) → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (g j) (U j)) :
    ∃ (σ : ℕ → ℕ) (V : ∀ j, Set (Fin (d (σ j)) → ℂ))
      (h : ∀ j, (Fin (d (σ j)) → ℂ) → (Fin n → ℂ)),
      (∀ j, V j ⊆ U (σ j)) ∧ (∀ j, IsOpen (V j)) ∧
      (∀ j, DifferentiableOn ℂ (h j) (V j)) ∧
      (∀ j t, t ∈ V j → F (h j t) = g (σ j) t) ∧
      F ⁻¹' (⋃ j, g j '' U j) = ⋃ j, h j '' V j :=
  bh15_lift_cover_aux n M F hloc d U g hU hg

/-- Two countable codimension-two covers interleave to cover their union.
Source: reindexing the disjoint union of two copies of the natural numbers. -/
theorem bh15_union_cover (n : ℕ) (A B : Set (Fin n → ℂ))
    (d₀ d₁ : ℕ → ℕ) (U₀ : ∀ j, Set (Fin (d₀ j) → ℂ))
    (U₁ : ∀ j, Set (Fin (d₁ j) → ℂ))
    (g₀ : ∀ j, (Fin (d₀ j) → ℂ) → (Fin n → ℂ))
    (g₁ : ∀ j, (Fin (d₁ j) → ℂ) → (Fin n → ℂ))
    (hd₀ : ∀ j, (U₀ j).Nonempty → d₀ j + 2 ≤ n)
    (hd₁ : ∀ j, (U₁ j).Nonempty → d₁ j + 2 ≤ n)
    (hU₀ : ∀ j, IsOpen (U₀ j)) (hU₁ : ∀ j, IsOpen (U₁ j))
    (hg₀ : ∀ j, DifferentiableOn ℂ (g₀ j) (U₀ j))
    (hg₁ : ∀ j, DifferentiableOn ℂ (g₁ j) (U₁ j))
    (hA : A = ⋃ j, g₀ j '' U₀ j) (hB : B = ⋃ j, g₁ j '' U₁ j) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, (U j).Nonempty → d j + 2 ≤ n) ∧
      (∀ j, IsOpen (U j)) ∧ (∀ j, DifferentiableOn ℂ (g j) (U j)) ∧
      A ∪ B = ⋃ j, g j '' U j :=
  bh15_union_cover_aux n A B d₀ d₁ U₀ U₁ g₀ g₁ hd₀ hd₁ hU₀ hU₁ hg₀ hg₁ hA hB

end HodgeLean.Adapters

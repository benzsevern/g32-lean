import HodgeLean.Foundations.Program.PrymVariationFramesProofs
import HodgeLean.Foundations.Program.PrymVariationFramesChecks

/-! # B6-3e: relative frames, holomorphic periods and the polarized variation

Implication from the B6-2b analytic total space, with parameter charts and holomorphic fibre
inclusions, and from holomorphic deck actions and original intersection forms on the actual
parameter fibres, to: local frames of relative holomorphic differentials, holomorphic periods
on transported integral classes, the identification of the transported saturated lattice with
the saturated period lattice, constancy of the original pairing, and a polarized weight-one
variation on the constant saturated lattice over an open parameter set. A linear-algebra
foundation for kernels of constant-rank analytic matrices is included. Every statement holds
at every parameter of `V`. Algebraic models, period coordinates, the Hermitian discriminant
and the Kodaira–Spencer comparison are not claimed; the packaging as a rational
`d1_PolarizedVHS` is assigned to stage 3f. These eight statements constitute stage 3e.
Stage 3f uses the output fibre by fibre; stage 3g also needs centre and K-action
compatibility, including Rosati and positivity, and B6-4 supplies period coordinates.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- A constant-rank analytic matrix family has a local analytic frame of its kernels.
Source: Lang, *Algebra*, rev. 3rd ed., Ch. XIII, §4, Cramer's rule, applied on a
nonvanishing maximal minor. -/
theorem b63e_analytic_kernel_frame {k m n r : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W)
    (M : (Fin k → ℂ) → Matrix (Fin m) (Fin n) ℂ)
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun u ↦ M u i j) W)
    (hr : ∀ u ∈ W, (M u).rank = r) (u₀ : Fin k → ℂ) (hu₀ : u₀ ∈ W) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ u₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ c : Fin (n - r) → (Fin k → ℂ) → (Fin n → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W') ∧
        ∀ u ∈ W', LinearIndependent ℂ (fun i ↦ c i u) ∧
          Submodule.span ℂ (Set.range fun i ↦ c i u) = LinearMap.ker (M u).mulVecLin :=
  b63e_analytic_kernel_frame_aux W hW M hM hr u₀ hu₀

example {k m n r : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W)
    (M : (Fin k → ℂ) → Matrix (Fin m) (Fin n) ℂ)
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun u ↦ M u i j) W)
    (hr : ∀ u ∈ W, (M u).rank = r) (u₀ : Fin k → ℂ) (hu₀ : u₀ ∈ W) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ u₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ c : Fin (n - r) → (Fin k → ℂ) → (Fin n → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W') ∧
        ∀ u ∈ W', LinearIndependent ℂ (fun i ↦ c i u) ∧
          Submodule.span ℂ (Set.range fun i ↦ c i u) = LinearMap.ker (M u).mulVecLin :=
  b63e_analytic_kernel_frame W hW M hM hr u₀ hu₀

/-- Periods of a relative differential on transported integral classes are holomorphic.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968), §1;
Ehresmann's fibration theorem for the proper submersion of the total space;
`b6m_period_comparison`, `b6m_homology_trivialization`. -/
theorem b63e_period_analytic (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hA : ∀ q : b6t_polydisc b × C, ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C),
      q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val)
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (U : Set (Fin 10 → ℂ)) (hU : IsOpen U) (θ : b63e_relForm b C V hV U) (s : V)
    (x : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    AnalyticOnNhd ℂ (b63e_periodFunction b C V hV P θ s x) (V ∩ U) :=
  b63e_period_analytic_aux b C V hV hVo hA hincl P hP U hU θ s x

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hA : ∀ q : b6t_polydisc b × C, ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C),
      q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val)
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (U : Set (Fin 10 → ℂ)) (hU : IsOpen U) (θ : b63e_relForm b C V hV U) (s : V)
    (x : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    AnalyticOnNhd ℂ (b63e_periodFunction b C V hV P θ s x) (V ∩ U) :=
  b63e_period_analytic b C V hV hVo hA hincl P hP U hU θ s x

/-- Transport and periods identify the saturated singular lattice at `s` with the saturated
period lattice at `t`, carrying the transported filtration to the primitive period filtration.
Source: `b63l_fibre_image_transport`, `b63l_period_image_comparison`, `b6m_period_comparison`;
Birkenhake–Lange, §12.2. -/
theorem b63e_lattice_period_transport (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) :
    ∃ E : b63l_parameterLattice b C hC V hV s ≃ₗ[ℤ]
        b63l_periodLattice (b63l_parameterFibre b C V hV t),
      (∀ x, (E x).val = b63e_transportMap b C hC V hV P s t x) ∧
      b63e_transportedF b C hC V hV P s t =
        (b63l_periodF (b63l_parameterFibre b C V hV t)).comap
          ((E : b63l_parameterLattice b C hC V hV s →ₗ[ℤ]
            b63l_periodLattice (b63l_parameterFibre b C V hV t)).baseChange ℂ) :=
  b63e_lattice_period_transport_aux b C hC V hV hG P hP s t

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) :
    ∃ E : b63l_parameterLattice b C hC V hV s ≃ₗ[ℤ]
        b63l_periodLattice (b63l_parameterFibre b C V hV t),
      (∀ x, (E x).val = b63e_transportMap b C hC V hV P s t x) ∧
      b63e_transportedF b C hC V hV P s t =
        (b63l_periodF (b63l_parameterFibre b C V hV t)).comap
          ((E : b63l_parameterLattice b C hC V hV s →ₗ[ℤ]
            b63l_periodLattice (b63l_parameterFibre b C V hV t)).baseChange ℂ) :=
  b63e_lattice_period_transport b C hC V hV hG P hP s t

/-- The original intersection pairings are constant under integral transport between fibres.
Source: `b6m_intersection_transport`, applied from the base surface to both fibres;
Farkas–Kra, *Riemann Surfaces*, Ch. III; Harris–Morrison, §1.G. -/
theorem b63e_pairing_constant (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) (x y : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    Q t (P t (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩) x))
        (P t (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩) y)) =
      Q s (P s x) (P s y) :=
  b63e_pairing_constant_aux b C V hV hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t x y

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) (x y : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    Q t (P t (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩) x))
        (P t (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩) y)) =
      Q s (P s x) (P s y) :=
  b63e_pairing_constant b C V hV hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t x y

/-- Every transported filtration is weight one on the fixed saturated lattice, polarized by the
constant original pairing.
Source: `b63l_image_riemann` with the two preceding comparisons; Birkenhake–Lange, §4.2, §5.3
and §12.2; Griffiths, *Periods of integrals on algebraic manifolds I*, §2. -/
theorem b63e_weight_one_riemann (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) :
    b2_IsWeightOne (b63l_parameterLattice b C hC V hV s)
        (b63e_transportedF b C hC V hV P s t) ∧
      b2_IsRiemannForm (b63l_parameterLattice b C hC V hV s)
        (b63e_transportedF b C hC V hV P s t) (b63e_singularQ b C hC V hV s (P s) (Q s)) :=
  b63e_weight_one_riemann_aux b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) :
    b2_IsWeightOne (b63l_parameterLattice b C hC V hV s)
        (b63e_transportedF b C hC V hV P s t) ∧
      b2_IsRiemannForm (b63l_parameterLattice b C hC V hV s)
        (b63e_transportedF b C hC V hV P s t) (b63e_singularQ b C hC V hV s (P s) (Q s)) :=
  b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t

end HodgeLean.Foundations.Program

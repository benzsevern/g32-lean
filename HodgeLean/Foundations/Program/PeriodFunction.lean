import HodgeLean.Foundations.Program.PeriodFunctionProofs

/-! # B6-4c: the period function

Stage B6-4c of `docs/specs/PeriodCoordinates.md`, drafted in `docs/specs/PeriodFunction.md`.
The period function `b64c_period M m V G` of a family `G` of filtrations of a lattice `M`,
marked by a rational marking `m`, is the chart coordinate of the marked filtration on `V` and
`0` off `V`; `b64c_geomPeriod` is the case of the transported period filtrations of B6-3e.
The file claims:

* analytic integral coefficients stay analytic after any complexified rational marking;
* the implication from local analytic frames and chart membership on an open `V` to
  analyticity of the period function on `V`, for every rational marking;
* the implication from a polarized `K`-linear rational marking, Riemann relations, dimension six
  and eigen-ranks `(3, 3)` on `V` to the chart identity `b60_F (period t) = marked F_t` and to
  `MapsTo period V 𝓗₃`;
* the transported filtration of B6-3e has dimension six and eigen-ranks `(3, 3)` at every pair
  of parameters;
* for every polarized `K`-linear rational marking of the saturated lattice at `s`, the
  geometric period function maps `V` into `𝓗₃` with the chart identity;
* the implication from local analytic frames of the transported filtrations to analyticity of
  the geometric period function on `V`, for every such marking.

These serve the fields `period`, `analytic` and `mapsTo` of `g32r_PeriodMap` (the chain check at
the end). The existence of the marking for the G32 lattice is the named obligation
`b64b_rational_marking`, set aside on the H7 discriminant theorem, never a binder. Statement 8,
analyticity of the geometric period function without frames, is set aside on
`b63e_filtration_frame` (relative-frame route); `b64c_geomPeriod_analytic_of_frames` gives it
from the frames, which it takes as an explicit binder. The first six statements are free of the
marking and of the frames; `b64c_geomPeriod_chart` is free of the frames. Nothing here constructs the marking, the isogenies, the Schlesinger
path, the jet or the codifferential. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers Filter Set
open scoped Manifold ContDiff TensorProduct Topology
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Analytic coefficients of a finite family of lattice vectors in an integral basis have
analytic eigen-coordinates after any complexified rational marking. It extends
`b64b_marked_frame_analytic` from six vectors and a basis of rank twelve to arbitrary finite
index types, which is the shape of the frames of `b63e_filtration_frame`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§1; Bourbaki, *Algebra*, Ch. II, §5, extension of scalars. -/
theorem b64c_marked_coord_analytic (M : Type*) [AddCommGroup M] {ι κ : Type} [Fintype ι]
    (B : Module.Basis ι ℤ M) (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (W : Set (Fin 10 → ℂ)) (c : κ → (Fin 10 → ℂ) → ι → ℂ)
    (hc : ∀ i, AnalyticOnNhd ℂ (c i) W) :
    ∀ i p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr
      (b64b_complexMarking M m (b63e_coordVector B (c i t))) p) W :=
  b64c_marked_coord_analytic_aux M B m W c hc

example (M : Type*) [AddCommGroup M] {ι κ : Type} [Fintype ι]
    (B : Module.Basis ι ℤ M) (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (W : Set (Fin 10 → ℂ)) (c : κ → (Fin 10 → ℂ) → ι → ℂ)
    (hc : ∀ i, AnalyticOnNhd ℂ (c i) W) :
    ∀ i p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr
      (b64b_complexMarking M m (b63e_coordVector B (c i t))) p) W :=
  b64c_marked_coord_analytic M B m W c hc

/-- The implication from local analytic frames of a family of filtrations over an open set
`V`, and chart membership of its marked filtrations on `V`, to analyticity of the period
function on `V`. It holds for every rational marking; no polarization is used.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, §1 (period maps in graph
coordinates); `b64_coordOf_analyticOnNhd`. -/
theorem b64c_period_analyticOnNhd (M : Type*) [AddCommGroup M] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℤ M) (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (V : Set (Fin 10 → ℂ)) (hV : IsOpen V) (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M))
    (hframe : ∀ t₀ ∈ V, ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀ ∈ W ∧ W ⊆ V ∧
      ∃ n : ℕ, ∃ c : Fin n → (Fin 10 → ℂ) → ι → ℂ, (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t ∈ W, Submodule.span ℂ (Set.range fun i => b63e_coordVector B (c i t)) = G t)
    (hchart : ∀ t ∈ V, ∃ z : Fin 9 → ℂ, b64c_markedF M m G t = b60_F z) :
    AnalyticOnNhd ℂ (b64c_period M m V G) V :=
  b64c_period_analyticOnNhd_aux M B m V hV G hframe hchart

example (M : Type*) [AddCommGroup M] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℤ M) (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (V : Set (Fin 10 → ℂ)) (hV : IsOpen V) (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M))
    (hframe : ∀ t₀ ∈ V, ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀ ∈ W ∧ W ⊆ V ∧
      ∃ n : ℕ, ∃ c : Fin n → (Fin 10 → ℂ) → ι → ℂ, (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t ∈ W, Submodule.span ℂ (Set.range fun i => b63e_coordVector B (c i t)) = G t)
    (hchart : ∀ t ∈ V, ∃ z : Fin 9 → ℂ, b64c_markedF M m G t = b60_F z) :
    AnalyticOnNhd ℂ (b64c_period M m V G) V :=
  b64c_period_analyticOnNhd M B m V hV G hframe hchart

/-- For a polarized `K`-linear rational marking and a family of Riemann filtrations of
dimension six with Hodge eigen-ranks `(3, 3)` on `V`, the chart filtration at the period is
the marked filtration, at every `t ∈ V`. This is the identity B6-4d consumes.
Source: van Geemen, LNM 1594, §§5.7–5.10; `b64b_marking_riemann`,
`b60c_fixed_filtration_chart`, `b64_coordOf_eq`. -/
theorem b64c_period_filtration (M : Type*) [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hQ : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (V : Set (Fin 10 → ℂ)) (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M))
    (hR : ∀ t ∈ V, b2_IsRiemannForm M (G t) Q)
    (hdim : ∀ t ∈ V, Module.finrank ℂ (G t) = 6)
    (hneg : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    ∀ t ∈ V, b60_F (b64c_period M m V G t) = b64c_markedF M m G t :=
  b64c_period_filtration_aux M Q A m hA hQ V G hR hdim hneg hpos

example (M : Type*) [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hQ : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (V : Set (Fin 10 → ℂ)) (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M))
    (hR : ∀ t ∈ V, b2_IsRiemannForm M (G t) Q)
    (hdim : ∀ t ∈ V, Module.finrank ℂ (G t) = 6)
    (hneg : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    ∀ t ∈ V, b60_F (b64c_period M m V G t) = b64c_markedF M m G t :=
  b64c_period_filtration M Q A m hA hQ V G hR hdim hneg hpos

/-- Under the hypotheses of `b64c_period_filtration`, the period function maps `V` into the
domain `𝓗₃` (`g32m_Domain`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §4.2; van Geemen, LNM 1594, §5.10;
`b64b_marking_riemann`, `b60c_fixed_filtration_chart`. -/
theorem b64c_period_mapsTo (M : Type*) [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hQ : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (V : Set (Fin 10 → ℂ)) (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M))
    (hR : ∀ t ∈ V, b2_IsRiemannForm M (G t) Q)
    (hdim : ∀ t ∈ V, Module.finrank ℂ (G t) = 6)
    (hneg : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    MapsTo (b64c_period M m V G) V (g32m_Domain : Set (Fin 9 → ℂ)) :=
  b64c_period_mapsTo_aux M Q A m hA hQ V G hR hdim hneg hpos

example (M : Type*) [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hQ : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (V : Set (Fin 10 → ℂ)) (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M))
    (hR : ∀ t ∈ V, b2_IsRiemannForm M (G t) Q)
    (hdim : ∀ t ∈ V, Module.finrank ℂ (G t) = 6)
    (hneg : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    MapsTo (b64c_period M m V G) V (g32m_Domain : Set (Fin 9 → ℂ)) :=
  b64c_period_mapsTo M Q A m hA hQ V G hR hdim hneg hpos

/-- The transported filtration of B6-3e has dimension six, for every pair of parameters.
Source: G32 v0.16, Proposition 3.1 and Lemma 3.3; `b63e_lattice_period_transport`,
`b63d_dim_eq`. -/
theorem b64c_transported_finrank (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) :
    Module.finrank ℂ (b63e_transportedF b C hC V hV P s t) = 6 :=
  b64c_transported_finrank_aux b C hC V hV hG hb f hk hsurj hgal hbranch hrot P hP s t

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) :
    Module.finrank ℂ (b63e_transportedF b C hC V hV P s t) = 6 :=
  b64c_transported_finrank b C hC V hV hG hb f hk hsurj hgal hbranch hrot P hP s t

/-- Both eigenspaces `∓ i√3` of the integral operator `1 + 2Z` meet the transported filtration
in dimension three, for every pair of parameters.
Source: G32 v0.16, Proposition 3.1 and Lemma 3.3 (Chevalley–Weil); `b63d_chevalleyWeil_hodge`,
`b63d_centre_transport`, `b63e_lattice_period_transport`. -/
theorem b64c_transported_eigen_ranks (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s : V) (A : b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s)
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV s x.val) (t : V) :
    Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (A.baseChange ℂ) (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
      Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (A.baseChange ℂ) (Complex.I * (Real.sqrt 3 : ℂ))) = 3 :=
  b64c_transported_eigen_ranks_aux b C hC V hV hG hb f hk hsurj hgal hbranch hrot P hP s A hA t

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s : V) (A : b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s)
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV s x.val) (t : V) :
    Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (A.baseChange ℂ) (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
      Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (A.baseChange ℂ) (Complex.I * (Real.sqrt 3 : ℂ))) = 3 :=
  b64c_transported_eigen_ranks b C hC V hV hG hb f hk hsurj hgal hbranch hrot P hP s A hA t

/-- For every polarized `K`-linear rational marking of the saturated singular lattice at `s`,
the geometric period function takes each `t ∈ V` into `𝓗₃`, and the chart filtration at its
value is the marked transported filtration. The existence of such a marking for the G32
lattice is `b64b_rational_marking`, which is set aside on the H7 discriminant theorem; this
statement quantifies over the marking and is free of the 3e frame statements.
Source: G32 v0.16, first paragraph of the proof of Theorem 7.2; `b63e_weight_one_riemann`,
`b64b_marking_riemann`, `b60c_fixed_filtration_chart`. -/
theorem b64c_geomPeriod_chart (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s : V) (A : b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s)
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV s x.val)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ b C hC V hV s (P s) (Q s)).baseChange ℚ x y) :
    ∀ t ∈ V, b64c_geomPeriod b C hC V hV P s m t ∈ g32m_Domain ∧
      b60_F (b64c_geomPeriod b C hC V hV P s m t) =
        b64c_markedF _ m (b64c_transportedFamily b C hC V hV P s) t :=
  b64c_geomPeriod_chart_aux b C hC V hV hG hb f hf hs hk hsurj hgal hbranch hrot Q₀ hQ₀ Q hQ P hP s A hA m hJ hpol

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s : V) (A : b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s)
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV s x.val)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ b C hC V hV s (P s) (Q s)).baseChange ℚ x y) :
    ∀ t ∈ V, b64c_geomPeriod b C hC V hV P s m t ∈ g32m_Domain ∧
      b60_F (b64c_geomPeriod b C hC V hV P s m t) =
        b64c_markedF _ m (b64c_transportedFamily b C hC V hV P s) t :=
  b64c_geomPeriod_chart b C hC V hV hG hb f hf hs hk hsurj hgal hbranch hrot Q₀ hQ₀ Q hQ P hP s A hA m hJ hpol

/-- Statement 8 in frame-premise form. For every polarized `K`-linear rational marking of the
saturated singular lattice at `s`, and local analytic frames of the transported filtrations in an
integral basis `B` of that lattice, the geometric period function is analytic on the open set `V`.
The frame premise `hframe` is the shape of `b63e_filtration_frame`, which stays set aside on the
relative-frame route; it is an explicit binder here. Like `b64c_geomPeriod_chart`, the statement
quantifies over the marking, whose existence for the G32 lattice is `b64b_rational_marking` (H7).
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, §1;
`b64c_period_analyticOnNhd`, `b64c_geomPeriod_chart`. -/
theorem b64c_geomPeriod_analytic_of_frames (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s : V) (A : b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s)
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV s x.val)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ b C hC V hV s (P s) (Q s)).baseChange ℚ x y)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice b C hC V hV s))
    (hframe : ∀ t₀ ∈ V, ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀ ∈ W ∧ W ⊆ V ∧
      ∃ n : ℕ, ∃ c : Fin n → (Fin 10 → ℂ) → Fin 12 → ℂ, (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t ∈ W, Submodule.span ℂ (Set.range fun i => b63e_coordVector B (c i t)) =
          b64c_transportedFamily b C hC V hV P s t) :
    AnalyticOnNhd ℂ (b64c_geomPeriod b C hC V hV P s m) V := by
  have hchart := b64c_geomPeriod_chart b C hC V hV hG hb f hf hs hk hsurj hgal hbranch
    hrot Q₀ hQ₀ Q hQ P hP s A hA m hJ hpol
  exact b64c_period_analyticOnNhd _ B m V hVo _ hframe
    (fun t ht => ⟨_, ((hchart t ht).2).symm⟩)

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s : V) (A : b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s)
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV s x.val)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ b C hC V hV s (P s) (Q s)).baseChange ℚ x y)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice b C hC V hV s))
    (hframe : ∀ t₀ ∈ V, ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀ ∈ W ∧ W ⊆ V ∧
      ∃ n : ℕ, ∃ c : Fin n → (Fin 10 → ℂ) → Fin 12 → ℂ, (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t ∈ W, Submodule.span ℂ (Set.range fun i => b63e_coordVector B (c i t)) =
          b64c_transportedFamily b C hC V hV P s t) :
    AnalyticOnNhd ℂ (b64c_geomPeriod b C hC V hV P s m) V :=
  b64c_geomPeriod_analytic_of_frames b C hC V hV hVo hG hb f hf hs hk hsurj hgal hbranch hrot Q₀ hQ₀
    Q hQ P hP s A hA m hJ hpol B hframe
/-- The integral coordinates of the frame vectors of the fixed chart, in the standard basis of
`ℤ[ω]⁶`, used by the instance checks. -/
private theorem b64c_coordVector_repr (x : ℂ ⊗[ℤ] b60_Lattice) :
    b63e_coordVector (Pi.basisFun ℤ (Fin 6 × Fin 2)) (fun j => b60_basis.repr x j) = x := by
  conv_rhs => rw [← b60_basis.sum_repr x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [b60_basis, Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Instance check for `b64c_period_analyticOnNhd`, with a nonconstant family of rank six:
the chart filtrations `b60_F (t₀, …, t₀)` over all of `ℂ¹⁰`, the identity marking, and the
global frame `b60_frame` written in the standard integral basis. Every hypothesis holds; the
filtration has dimension six at every parameter and takes different values at `0` and at
`(1, …, 1)`. -/
example :
    let φ : (Fin 10 → ℂ) → Fin 9 → ℂ := fun t _ => t 0
    let G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice) := fun t => b60_F (φ t)
    (∀ t₀ ∈ (Set.univ : Set (Fin 10 → ℂ)), ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀ ∈ W ∧
      W ⊆ Set.univ ∧ ∃ n : ℕ, ∃ c : Fin n → (Fin 10 → ℂ) → (Fin 6 × Fin 2) → ℂ,
        (∀ i, AnalyticOnNhd ℂ (c i) W) ∧ ∀ t ∈ W, Submodule.span ℂ
          (Set.range fun i => b63e_coordVector (Pi.basisFun ℤ (Fin 6 × Fin 2)) (c i t)) = G t) ∧
    (∀ t ∈ (Set.univ : Set (Fin 10 → ℂ)), ∃ z : Fin 9 → ℂ,
      b64c_markedF b60_Lattice (LinearEquiv.refl ℚ _) G t = b60_F z) ∧
    (∀ t, Module.finrank ℂ (G t) = 6) ∧ G 0 ≠ G (fun _ => 1) := by
  intro φ G
  let c : Fin 6 → (Fin 10 → ℂ) → (Fin 6 × Fin 2) → ℂ := fun i t j =>
    b60_basis.repr (b60_frame (φ t) (finProdFinEquiv.symm i)) j
  have hc : ∀ i, AnalyticOnNhd ℂ (c i) Set.univ := by
    intro i
    refine analyticOnNhd_pi_iff.2 fun j => ?_
    intro t _
    have hp : AnalyticAt ℂ (fun t : Fin 10 → ℂ => t 0) t :=
      (ContinuousLinearMap.proj (0 : Fin 10) : (Fin 10 → ℂ) →L[ℂ] ℂ).analyticAt t
    simp only [φ, b60_frame]
    split_ifs <;>
      simp only [map_add, map_sum, map_smul, Finsupp.add_apply, Finsupp.coe_finsetSum,
        Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, g32m_toMat, Matrix.of_apply,
        ← Finset.mul_sum] <;>
      exact analyticAt_const.add (hp.mul analyticAt_const)
  refine ⟨fun t₀ _ => ⟨Set.univ, isOpen_univ, trivial, subset_rfl, 6, c, hc, fun t _ => ?_⟩,
    fun t _ => ⟨φ t, b64c_markedF_refl G t⟩, fun t => ?_, fun h => ?_⟩
  · have hv : (fun i => b63e_coordVector (Pi.basisFun ℤ (Fin 6 × Fin 2)) (c i t)) =
        b60_frame (φ t) ∘ finProdFinEquiv.symm := by
      funext i
      exact b64c_coordVector_repr _
    rw [hv, finProdFinEquiv.symm.surjective.range_comp]
    rfl
  · change Module.finrank ℂ (b60_F (φ t)) = 6
    rw [b60_F, finrank_span_eq_card (b60_frame_independent _)]
    rfl
  · have h1 := congrArg b64_coordOf h
    change b64_coordOf (b60_F (φ 0)) = b64_coordOf (b60_F (φ fun _ => 1)) at h1
    rw [b64_coordOf_eq, b64_coordOf_eq] at h1
    have h2 := congrFun h1 0
    norm_num [φ] at h2

/-- Instance check for `b64c_period_filtration` and `b64c_period_mapsTo`, with a nonidentity
marking and a nonconstant family of rank six: the fixed lattice with `Q = b60_E`, `A = ω`, the
marking `-id`, and the chart filtrations `b60_F (t₀, …, t₀)` over the open preimage `V` of the
domain. Every hypothesis holds, `V` contains `0`, and the filtration is not constant on `V`. -/
example :
    let φ : (Fin 10 → ℂ) → Fin 9 → ℂ := fun t _ => t 0
    let V : Set (Fin 10 → ℂ) := φ ⁻¹' (g32m_Domain : Set (Fin 9 → ℂ))
    let G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice) := fun t => b60_F (φ t)
    let m : (ℚ ⊗[ℤ] b60_Lattice) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice) := LinearEquiv.neg ℚ
    (∃ x, m x ≠ x) ∧
    (∀ x, m (b60_omega.baseChange ℚ x) = b60_omega.baseChange ℚ (m x)) ∧
    (∀ x y, b60_E.baseChange ℚ (m x) (m y) = b60_E.baseChange ℚ x y) ∧
    (∀ t ∈ V, b2_IsRiemannForm b60_Lattice (G t) b60_E) ∧
    (∀ t ∈ V, Module.finrank ℂ (G t) = 6) ∧
    (∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (b60_omega.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3) ∧
    (∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (b60_omega.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) ∧
    IsOpen V ∧ (0 : Fin 10 → ℂ) ∈ V ∧ ∃ t ∈ V, G t ≠ G 0 := by
  intro φ V G m
  have hφ : Continuous φ := continuous_pi fun _ => continuous_apply 0
  have hVo : IsOpen V := g32m_Domain.isOpen.preimage hφ
  have h0 : (0 : Fin 10 → ℂ) ∈ V := by
    show (0 : Fin 9 → ℂ) ∈ g32m_Domain
    exact g32m_zero_mem
  let B := (Pi.basisFun ℤ (Fin 6 × Fin 2)).baseChange ℚ
  refine ⟨⟨B (0, 0), fun h => ?_⟩, fun x => ?_, fun x y => ?_,
    fun t ht => (b60_riemann_iff (φ t)).2 ht, fun t _ => ?_,
    fun t _ => (b60_weil_dimensions (φ t)).2, fun t _ => (b60_weil_dimensions (φ t)).1,
    hVo, h0, ?_⟩
  · have hh := congrArg (fun x => B.repr x (0, 0)) h
    norm_num only [m, LinearEquiv.neg_apply, map_neg, Module.Basis.repr_self,
      Finsupp.single_eq_same, Finsupp.neg_apply] at hh
  · simp only [m, LinearEquiv.neg_apply, map_neg]
  · simp only [m, LinearEquiv.neg_apply, map_neg, LinearMap.neg_apply, neg_neg]
  · change Module.finrank ℂ (b60_F (φ t)) = 6
    rw [b60_F, finrank_span_eq_card (b60_frame_independent _)]
    rfl
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hVo 0 h0
    refine ⟨fun _ => ((ε / 2 : ℝ) : ℂ), hball ?_, fun h => ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      refine lt_of_le_of_lt (pi_norm_const_le _) ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · have h1 := congrArg b64_coordOf h
      change b64_coordOf (b60_F (φ fun _ => ((ε / 2 : ℝ) : ℂ))) =
        b64_coordOf (b60_F (φ 0)) at h1
      rw [b64_coordOf_eq, b64_coordOf_eq] at h1
      have h2 := congrFun h1 0
      simp only [φ, Pi.zero_apply, Complex.ofReal_eq_zero] at h2
      linarith

/-- The geometric period function vanishes off the parameter set, by definition; on `V` it is
the coordinate of the marked transported filtration (`PeriodFunctionDefs.lean`). -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s : V)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (u : Fin 10 → ℂ) (hu : u ∉ V) :
    b64c_geomPeriod b C hC V hV P s m u = 0 := by
  simp [b64c_geomPeriod, b64c_period, hu]
/-- **Chain check toward `g32r_PeriodMap`.** With the geometric period function of a
polarized `K`-linear rational marking of the saturated lattice at `s`, the fields `period`,
`analytic` and `mapsTo` come from `b64c_geomPeriod_analytic_of_frames` and
`b64c_geomPeriod_chart`. `analytic` is reached from the frames: the integral basis `B` and the
local analytic frames `hframe` of the transported filtrations (the shape of
`b63e_filtration_frame`, set aside on the relative-frame route) are a named input. The
remaining fields enter as explicit binders, each stated with this `period`: `isog` is B6-4d,
`curve`, `jet` and `jet_certified` are B6-5, and `codiff` is B6-6. The marking itself is the
obligation `b64b_rational_marking` (H7); it is a variable here, never chosen. -/
example (Fm : g32m_UniversalFamily) (Pf : g32h_PrymFamily) (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s : V) (A : b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s)
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV s x.val)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ b C hC V hV s (P s) (Q s)).baseChange ℚ x y)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice b C hC V hV s))
    (hframe : ∀ t₀ ∈ V, ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀ ∈ W ∧ W ⊆ V ∧
      ∃ n : ℕ, ∃ c : Fin n → (Fin 10 → ℂ) → Fin 12 → ℂ, (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t ∈ W, Submodule.span ℂ (Set.range fun i => b63e_coordVector B (c i t)) =
          b64c_transportedFamily b C hC V hV P s t)
    (hisog : ∀ t (_ : t ∈ V) (hm : b64c_geomPeriod b C hC V hV P s m t ∈ g32m_Domain),
      ∃ s', g32t_KIsog (Pf.fiber s') (Fm.univ ⟨b64c_geomPeriod b C hC V hV P s m t, hm⟩))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0) (curve_zero : curve 0 ∈ V)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ R : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit R ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b64c_geomPeriod b C hC V hV P s m) (curve θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * R) :
    Nonempty (g32r_PeriodMap Fm Pf) := by
  have hmaps : MapsTo (b64c_geomPeriod b C hC V hV P s m) V (g32m_Domain : Set (Fin 9 → ℂ)) := fun t ht =>
    (b64c_geomPeriod_chart b C hC V hV hG hb f hf hs hk hsurj hgal hbranch hrot Q₀ hQ₀ Q hQ P hP s A hA m hJ hpol t ht).1
  exact ⟨{ V := V
           isOpen_V := hVo
           period := b64c_geomPeriod b C hC V hV P s m
           analytic := b64c_geomPeriod_analytic_of_frames b C hC V hV hVo hG hb f hf hs hk hsurj
             hgal hbranch hrot Q₀ hQ₀ Q hQ P hP s A hA m hJ hpol B hframe
           mapsTo := hmaps
           isog := fun t ht => hisog t ht (hmaps ht)
           curve := curve
           curve_cont := curve_cont
           curve_zero := curve_zero
           jet := jet
           jet_certified := jet_certified
           codiff := codiff }⟩

/-- **Chain check of the dimension inputs.** On the transported family, statements
`b64c_transported_finrank` and `b64c_transported_eigen_ranks` give, at every `t ∈ V`, the
dimension and eigen-rank hypotheses of `b64c_period_filtration` and `b64c_period_mapsTo`. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s : V) (A : b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s)
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV s x.val) :
    (∀ t ∈ V, Module.finrank ℂ (b64c_transportedFamily b C hC V hV P s t) = 6) ∧
    (∀ t ∈ V, Module.finrank ℂ ↥(b64c_transportedFamily b C hC V hV P s t ⊓
      Module.End.eigenspace (A.baseChange ℂ) (-Complex.I * (Real.sqrt 3 : ℂ))) = 3) ∧
    (∀ t ∈ V, Module.finrank ℂ ↥(b64c_transportedFamily b C hC V hV P s t ⊓
      Module.End.eigenspace (A.baseChange ℂ) (Complex.I * (Real.sqrt 3 : ℂ))) = 3) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [show b64c_transportedFamily b C hC V hV P s t =
      b63e_transportedF b C hC V hV P s ⟨t, ht⟩ by simp [b64c_transportedFamily, ht]]
    exact b64c_transported_finrank b C hC V hV hG hb f hk hsurj hgal hbranch hrot P hP s ⟨t, ht⟩
  · rw [show b64c_transportedFamily b C hC V hV P s t =
      b63e_transportedF b C hC V hV P s ⟨t, ht⟩ by simp [b64c_transportedFamily, ht]]
    exact (b64c_transported_eigen_ranks b C hC V hV hG hb f hk hsurj hgal hbranch hrot P hP
      s A hA ⟨t, ht⟩).1
  · rw [show b64c_transportedFamily b C hC V hV P s t =
      b63e_transportedF b C hC V hV P s ⟨t, ht⟩ by simp [b64c_transportedFamily, ht]]
    exact (b64c_transported_eigen_ranks b C hC V hV hG hb f hk hsurj hgal hbranch hrot P hP
      s A hA ⟨t, ht⟩).2

end HodgeLean.Foundations.Program

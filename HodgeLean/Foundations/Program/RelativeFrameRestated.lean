import HodgeLean.Foundations.Program.RelativeFrameRestatedProofs
import HodgeLean.Foundations.Program.RelativeFrameCharts
import HodgeLean.Foundations.Program.RelativeFrameElliptic
import HodgeLean.Foundations.Program.PrymVariationFrames

/-! # Relative frames restated (D2–D4): statement draft
Implications, for a family that carries a plumbing datum over `V` (`rf5_FamilyPlumbing`, the C12
family datum), from the frozen premises of the three set-aside B6-3e statements to their frozen
conclusions: from the B6-2b total-space premises (`hA`, `hincl`, compact connected Hausdorff
fibres, `V` open) to local frames of relative holomorphic differentials whose fibre values are
bases (D2, restating `b63e_relForm_frame`); with holomorphic deck actions, intersection forms and
integral period comparisons in addition, to local frames of the transported primitive filtration
with analytic integral coordinates (D3, restating `b63e_filtration_frame`); and with the base
surface data in addition, to a polarized weight-one variation on the constant saturated lattice
over `V` (D4, restating `b63e_polarized_variation`). Each restated statement has the frozen
binders and conclusion of the original and adds only the family datum (with the analytic
structure on the base surface that its type needs). None carries a kernel hypothesis.

Not claimed: the construction of `rf5_FamilyPlumbing` for the B6-2b family (stage B on the total
space, including the off-centre puncture classifier), which is neither supplied nor assumed here;
the rational packaging `d1_PolarizedVHS` of B6-3g part 6; B6-4c statement 8 itself. HC no
distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- D2, the restatement of `b63e_relForm_frame` for families with a plumbing datum: near every
parameter there are `g = finrank Ω¹(X_{t₀})` relative holomorphic differentials whose fibre values
are a basis of `Ω¹(X_t)` at every nearby `t`. The proof is the structural proof of the original
with D1 (`rf5_relForm_extend`) in place of the helper `b63e_relForm_extend`: extend a basis of
`Ω¹(X_{t₀})`, keep independence near `t₀` (`b63e_relForm_independent_near`, which uses `hA`), and
conclude by the constant genus (`b63e_holForm_finrank_homeomorph`).
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §5, D2; `rf5_relForm_extend`,
`b63e_relForm_independent_near`; Griffiths, *Periods of integrals on algebraic manifolds I*,
Amer. J. Math. 90 (1968), §1. -/
theorem rf6_relForm_frame (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
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
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV)
    (t₀ : V) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
      ∃ θ : Fin (Module.finrank ℂ (b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀))) →
          b63e_relForm b C V hV W,
        ∀ t : V, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_relFormAt b C V hV (θ i) t) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_relFormAt b C V hV (θ i) t) = ⊤ :=
  rf6_relForm_frame_aux b C V hV hVo hA hincl F t₀

example := @rf6_relForm_frame

/-- D3, the restatement of `b63e_filtration_frame` for families with a plumbing datum: the
transported primitive filtration `F_{s,t} ⊆ ℂ ⊗ Λ_s` has, near every parameter, a frame with
analytic integral coordinates in any integral basis `B` of `Λ_s`. The proof is the structural
proof of the original with D2 for `b63e_relForm_frame`: the periods of the frame of D2 on `B` form
an analytic matrix (`b63e_period_analytic`) whose kernel is `F_{s,t}` (`b63e_period_matrix_kernel`)
of constant dimension (weight one, `b63e_lattice_period_transport`, `b63l_image_riemann`), and
`b63e_kernel_frame_of_nullity` gives the analytic kernel frame.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §5, D3; Griffiths, *Periods of integrals on
algebraic manifolds I*, Amer. J. Math. 90 (1968), §1; `rf6_relForm_frame`. -/
theorem rf6_filtration_frame (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
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
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV)
    (s : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s))
    (t₀ : V) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
      ∃ c : Fin (Module.finrank ℂ (b63e_transportedF b C hC V hV P s t₀)) →
          (Fin 10 → ℂ) → (ι → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t : V, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_coordVector B (c i t.val)) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_coordVector B (c i t.val)) =
            b63e_transportedF b C hC V hV P s t :=
  rf6_filtration_frame_aux b C hC V hV hVo hA hincl hG Q hQ P hP F s B t₀

example := @rf6_filtration_frame

/-- D4, the restatement of `b63e_polarized_variation` for families with a plumbing datum: the
transported primitive filtrations and the constant original pairing form a polarized weight-one
variation on the constant saturated lattice over `V`. The proof is the structural proof of the
original: holomorphy from the frames of D3 (`b63e_const_subbundle_of_frames`), weight one and the
Riemann relations from the checked `b63e_weight_one_riemann`.
Source: Griffiths, *Periods of integrals on algebraic manifolds III*, Publ. Math. IHÉS 38 (1970),
§§1–3; Deligne, *Théorie de Hodge II*, §4.4; `docs/specs/RelativeFrame.md` on `spec/relA`, §5, D4;
`rf6_filtration_frame`, `b63e_weight_one_riemann`. -/
theorem rf6_polarized_variation (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
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
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV)
    (s : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s)) :
    b2_IsPolarizedTorusFamily (Fin 10 → ℂ) (b63e_localSystem b C hC V hV hVo s B)
      (fun t ↦ b63e_transportedF b C hC V hV P s ⟨t.val, t.property⟩)
      (fun _ ↦ b63e_singularQ b C hC V hV s (P s) (Q s)) :=
  rf6_polarized_variation_aux b C hC V hV hVo hA hincl hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP F s B

example := @rf6_polarized_variation

/-! ## The original conclusions

Each `example` below has the binders of the set-aside original in their frozen order, followed by
the extra hypotheses of the restatement, and the original's frozen conclusion. The extra
hypotheses are, for D2 and D3, the analytic structure `[ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]`
on the base surface, outer data `D` on it and the family datum `F`; for D4, which already has
that structure on `C`, only `D` and `F`. No restatement adds `hA` (all three originals have it)
or a kernel hypothesis. -/

/-- D2 gives the conclusion of `b63e_relForm_frame` on every input with a family datum. -/
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
    (t₀ : V)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
      ∃ θ : Fin (Module.finrank ℂ (b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀))) →
          b63e_relForm b C V hV W,
        ∀ t : V, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_relFormAt b C V hV (θ i) t) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_relFormAt b C V hV (θ i) t) = ⊤ :=
  rf6_relForm_frame b C V hV hVo hA hincl F t₀

/-- D3 gives the conclusion of `b63e_filtration_frame` on every input with a family datum. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
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
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s))
    (t₀ : V)
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
      ∃ c : Fin (Module.finrank ℂ (b63e_transportedF b C hC V hV P s t₀)) →
          (Fin 10 → ℂ) → (ι → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t : V, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_coordVector B (c i t.val)) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_coordVector B (c i t.val)) =
            b63e_transportedF b C hC V hV P s t :=
  rf6_filtration_frame b C hC V hV hVo hA hincl hG Q hQ P hP F s B t₀

/-- D4 gives the conclusion of `b63e_polarized_variation` on every input with a family datum. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
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
    (s : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s))
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV) :
    b2_IsPolarizedTorusFamily (Fin 10 → ℂ) (b63e_localSystem b C hC V hV hVo s B)
      (fun t ↦ b63e_transportedF b C hC V hV P s ⟨t.val, t.property⟩)
      (fun _ ↦ b63e_singularQ b C hC V hV s (P s) (Q s)) :=
  rf6_polarized_variation b C hC V hV hVo hA hincl hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP F s B

/-! ## Chain check

The fields served are the conclusions of the three set-aside statements, through which B6-4c's
frame premise and B6-3g part 6 are reached. The three structural proofs run here as dependency
chains: D1 gives D2, D2 gives D3, and D3 gives D4, each with checked results of B6-3e for the
other steps. They pass through open statements of this draft and of C12; they construct no frame
here. -/

set_option maxHeartbeats 400000 in
/-- D1 gives D2: the structural proof of `b63e_relForm_frame` with `rf5_relForm_extend`. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
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
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV)
    (t₀ : V) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
      ∃ θ : Fin (Module.finrank ℂ (b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀))) →
          b63e_relForm b C V hV W,
        ∀ t : V, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_relFormAt b C V hV (θ i) t) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_relFormAt b C V hV (θ i) t) = ⊤ := by
  classical
  let _ : ∀ t : V, FiniteDimensional ℂ (b3_HolForm ℂ (b63l_parameterFibre b C V hV t)) :=
    fun t ↦ b3_holForm_finiteDimensional (show Module.finrank ℂ ℂ = 1 by simp)
  let β := Module.finBasis ℂ (b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀))
  choose U hU htU hUV θ hθ using fun i ↦ rf5_relForm_extend hVo hincl F t₀ (β i)
  let W := V ∩ ⋂ i, U i
  have hW : IsOpen W := hVo.inter (isOpen_iInter_of_finite hU)
  have htW : t₀.val ∈ W := ⟨t₀.property, Set.mem_iInter.mpr htU⟩
  have hWi i : W ⊆ U i := fun u hu ↦ Set.mem_iInter.mp hu.2 i
  let θW i : b63e_relForm b C V hV W :=
    ⟨(θ i).val, b63e_relForm_mono b C V hV (hWi i) (θ i).property⟩
  have hβ : (fun i ↦ b63e_relFormAt b C V hV (θW i) t₀) = β := funext hθ
  have hli : LinearIndependent ℂ (fun i ↦ b63e_relFormAt b C V hV (θW i) t₀) := by
    rw [hβ]
    exact β.linearIndependent
  obtain ⟨W', hW', ht', hsub, hind⟩ :=
    b63e_relForm_independent_near b C V hV hVo hA hincl t₀ W hW htW θW hli
  let θ' i : b63e_relForm b C V hV W' :=
    ⟨(θW i).val, b63e_relForm_mono b C V hV (fun u hu ↦ (hsub hu).2) (θW i).property⟩
  refine ⟨W', hW', ht', fun u hu ↦ (hsub hu).1, θ', ?_⟩
  intro t ht
  have hi := hind t ht
  refine ⟨hi, hi.span_eq_top_of_card_eq_finrank' ?_⟩
  rw [Fintype.card_fin]
  exact b63e_holForm_finrank_homeomorph _ _
    (b6m_transport b C ⟨t₀.val, hV t₀.property⟩ ⟨t.val, hV t.property⟩)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- D2 gives D3: the structural proof of `b63e_filtration_frame` (`8e00f8f99`,
`PrymVariationFramesProofs.lean:250`) with `rf6_relForm_frame` for `b63e_relForm_frame`. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
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
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV)
    (s : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s))
    (t₀ : V) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
      ∃ c : Fin (Module.finrank ℂ (b63e_transportedF b C hC V hV P s t₀)) →
          (Fin 10 → ℂ) → (ι → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t : V, t.val ∈ W →
          LinearIndependent ℂ (fun i ↦ b63e_coordVector B (c i t.val)) ∧
          Submodule.span ℂ (Set.range fun i ↦ b63e_coordVector B (c i t.val)) =
            b63e_transportedF b C hC V hV P s t := by
  classical
  let L := b63l_parameterLattice b C hC V hV s
  have key : ∀ {n : ℕ} (B' : Module.Basis (Fin n) ℤ L),
      ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
        ∃ c : Fin (Module.finrank ℂ (b63e_transportedF b C hC V hV P s t₀)) →
            (Fin 10 → ℂ) → (Fin n → ℂ),
          (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
          ∀ t : V, t.val ∈ W →
            LinearIndependent ℂ (fun i ↦ b63e_coordVector B' (c i t.val)) ∧
            Submodule.span ℂ (Set.range fun i ↦ b63e_coordVector B' (c i t.val)) =
              b63e_transportedF b C hC V hV P s t := by
    intro n B'
    let _ : Module.Free ℤ L := Module.Free.of_basis B'
    let _ : Module.Finite ℤ L := Module.Finite.of_basis B'
    let Fs := b63e_transportedF b C hC V hV P s
    let e : (Fin n → ℂ) ≃ₗ[ℂ] (ℂ ⊗[ℤ] L) := (B'.baseChange ℂ).equivFun.symm
    have hw (t : V) : b2_IsWeightOne L (Fs t) := by
      obtain ⟨E, _, hF⟩ := b63e_lattice_period_transport b C hC V hV hG P hP s t
      rw [show Fs t = _ from hF]
      exact b63e_weightOne_comap E _
        (b63l_image_riemann (b63l_parameterFibre b C V hV t) (hG t) (Q t) (hQ t)).2.1
    have hd (t : V) : Module.finrank ℂ (Fs t) = Module.finrank ℂ (Fs t₀) := by
      have h := Submodule.finrank_add_eq_of_isCompl (hw t)
      have h₀ := Submodule.finrank_add_eq_of_isCompl (hw t₀)
      rw [b2a_finrank_conjSubmodule] at h h₀
      omega
    obtain ⟨W, hW, ht₀, hWV, θ, hθ⟩ := rf6_relForm_frame b C V hV hVo hA hincl F t₀
    let N : (Fin 10 → ℂ) → Matrix
        (Fin (Module.finrank ℂ (b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀))))
        (Fin n) ℂ := fun u i j ↦ b63e_periodFunction b C V hV P (θ i) s (B' j).val u
    have hN i j : AnalyticOnNhd ℂ (fun u ↦ N u i j) W :=
      (b63e_period_analytic b C V hV hVo hA hincl P hP W hW (θ i) s (B' j).val).mono
        (fun _ hu ↦ ⟨hWV hu, hu⟩)
    have hk (t : V) (ht : t.val ∈ W) :
        (Fs t).comap e.toLinearMap = LinearMap.ker (N t.val).mulVecLin := by
      have hNt : N t.val = fun i j ↦
          (b63e_transportMap b C hC V hV P s t (B' j)).val
            (b63e_relFormAt b C V hV (θ i) t) := by
        funext i j
        dsimp [N, b63e_periodFunction]
        rw [dite_eq_left t.property]
        rfl
      rw [hNt]
      ext c
      change (B'.baseChange ℂ).equivFun.symm c ∈ Fs t ↔ _
      rw [← b63e_coordVector_equiv]
      exact b63e_period_matrix_kernel (b63l_parameterFibre b C V hV t) B'
        (b63e_transportMap b C hC V hV P s t)
        (fun i ↦ b63e_relFormAt b C V hV (θ i) t) (hθ t ht).2 c
    have hn u (hu : u ∈ W) :
        Module.finrank ℂ (LinearMap.ker (N u).mulVecLin) = Module.finrank ℂ (Fs t₀) := by
      rw [← hk ⟨u, hWV hu⟩ hu]
      rw [← Submodule.map_equiv_eq_comap_symm]
      rw [LinearEquiv.finrank_map_eq]
      exact hd ⟨u, hWV hu⟩
    obtain ⟨W', hW', ht', hsub, c, hc, hspan⟩ :=
      b63e_kernel_frame_of_nullity W hW N hN hn t₀.val ht₀
    refine ⟨W', hW', ht', hsub.trans hWV, c, hc, ?_⟩
    intro t ht
    obtain ⟨hli, hsp⟩ := hspan t.val ht
    simp_rw [b63e_coordVector_equiv]
    refine ⟨hli.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective), ?_⟩
    change Submodule.span ℂ (Set.range (e.toLinearMap ∘ (fun i ↦ c i t.val))) = Fs t
    rw [Set.range_comp, ← Submodule.map_span, hsp, ← hk t (hsub ht)]
    exact Submodule.map_comap_eq_of_surjective e.surjective _
  let e := Fintype.equivFin ι
  obtain ⟨W, hW, ht, hWV, c, hc, hspan⟩ := key (B.reindex e)
  refine ⟨W, hW, ht, hWV, (fun i u j ↦ c i u (e j)), ?_, ?_⟩
  · intro i u hu
    exact AnalyticAt.pi fun j ↦ (analyticAt_pi_iff.mp (hc i u hu)) (e j)
  · intro t ht
    have heq (i) : b63e_coordVector B (fun j ↦ c i t.val (e j)) =
        b63e_coordVector (B.reindex e) (c i t.val) :=
      (b63e_coordVector_reindex B e (c i t.val)).symm
    simp_rw [heq]
    exact hspan t ht

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- D3 gives D4: the structural proof of `b63e_polarized_variation` (`8e00f8f99`,
`PrymVariationFramesProofs.lean:391`) with `rf6_filtration_frame` for `b63e_filtration_frame`. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
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
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV)
    (s : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s)) :
    b2_IsPolarizedTorusFamily (Fin 10 → ℂ) (b63e_localSystem b C hC V hV hVo s B)
      (fun t ↦ b63e_transportedF b C hC V hV P s ⟨t.val, t.property⟩)
      (fun _ ↦ b63e_singularQ b C hC V hV s (P s) (Q s)) := by
  let _ : Module.Free ℤ (b63l_parameterLattice b C hC V hV s) := Module.Free.of_basis B
  let _ : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s) := Module.Finite.of_basis B
  refine ⟨?_, fun _ _ _ _ _ ↦ rfl, ?_, ?_⟩
  · apply b63e_const_subbundle_of_frames (⟨V, hVo⟩ : TopologicalSpace.Opens (Fin 10 → ℂ)) B
    intro t₀
    obtain ⟨W, hW, ht, _, c, hc, hspan⟩ :=
      rf6_filtration_frame b C hC V hV hVo hA hincl hG Q hQ P hP F s B t₀
    exact ⟨W, hW, ht, _, c, hc, fun t ht ↦ (hspan t ht).2⟩
  · intro t
    exact (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t).1
  · intro t
    exact (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t).2

/-- D3 supplies the frame premise `hframe` of B6-4c's `b64c_geomPeriod_analytic_of_frames`
(`PeriodFunction.lean` on `spec/b64cm`), in its exact shape: for an integral basis of `Λ_s`
indexed by `Fin 12`, near every `t₀ ∈ V` analytic integral coordinates whose vectors span the
transported filtration at every nearby parameter. `rf6_transportedFamily` is the family
`b64c_transportedFamily` of that file, by the same definition. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
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
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    {O : Set C} {D : rf4_OuterData C O} (F : rf5_FamilyPlumbing b C D V hV)
    (s : V) (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice b C hC V hV s)) :
    ∀ t₀ ∈ V, ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀ ∈ W ∧ W ⊆ V ∧
      ∃ n : ℕ, ∃ c : Fin n → (Fin 10 → ℂ) → Fin 12 → ℂ, (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t ∈ W, Submodule.span ℂ (Set.range fun i => b63e_coordVector B (c i t)) =
          rf6_transportedFamily b C hC V hV P s t := by
  intro t₀ ht₀
  obtain ⟨W, hW, ht, hWV, c, hc, hspan⟩ :=
    rf6_filtration_frame b C hC V hV hVo hA hincl hG Q hQ P hP F s B ⟨t₀, ht₀⟩
  refine ⟨W, hW, ht, hWV, _, c, hc, fun t htW ↦ ?_⟩
  rw [rf6_transportedFamily, dite_eq_left (hWV htW)]
  exact (hspan ⟨t, hWV htW⟩ htW).2

/-! ## Satisfiable instance at rank one: D2 on the genus-one witness

The constant family `rfw_family b` over the elliptic curve `rfw_E` (`spec/ellw`) satisfies every
premise of `rf6_relForm_frame`: the polydisc is open, the total space carries product charts and is
an analytic manifold, the fibres are compact, connected and Hausdorff Riemann surfaces with
holomorphic inclusions, every point lies in a fibre-preserving atlas chart, and the family datum
exists. Each of these is a checked declaration. The fibres have genus one (`rfw_holForm_finrank`,
frozen on `spec/ellw`, and `b63e_holForm_finrank_homeomorph`), so the frame of D2 has one element
at every parameter: the rank is not zero. -/

/-- The premises of D2 hold on the genus-one family, from checked declarations only. -/
example (b : Fin 10 → ℂ) :
    IsOpen (b6t_polydisc b) ∧
    Nonempty (rf5_FamilyPlumbing b rfw_E rfw_outer (b6t_polydisc b) subset_rfl) ∧
    (∀ q : b6t_polydisc b × rfw_E, ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × rfw_E),
        q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val) ∧
    (∀ t : b6t_polydisc b, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b rfw_E (b6t_polydisc b) subset_rfl t ↦ x.val)) :=
  ⟨rf5_polydisc_isOpen b, ⟨rfw_family b⟩, rfw_fibreCharts b, fun t ↦ rfw_incl b t⟩

/-- D2 at rank one on the genus-one family: a frame of one relative form near every parameter,
whose fibre values are bases. A dependency chain through `rf6_relForm_frame` and
`rfw_holForm_finrank`. -/
example (b : Fin 10 → ℂ) (t₀ : b6t_polydisc b) :
    Module.finrank ℂ (b3_HolForm ℂ (b63l_parameterFibre b rfw_E (b6t_polydisc b) subset_rfl t₀))
        = 1 ∧
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ b6t_polydisc b ∧
      ∃ θ : Fin (Module.finrank ℂ
            (b3_HolForm ℂ (b63l_parameterFibre b rfw_E (b6t_polydisc b) subset_rfl t₀))) →
          b63e_relForm b rfw_E (b6t_polydisc b) subset_rfl W,
        ∀ t : b6t_polydisc b, t.val ∈ W →
          LinearIndependent ℂ
            (fun i ↦ b63e_relFormAt b rfw_E (b6t_polydisc b) subset_rfl (θ i) t) ∧
          Submodule.span ℂ (Set.range fun i ↦
            b63e_relFormAt b rfw_E (b6t_polydisc b) subset_rfl (θ i) t) = ⊤ :=
  ⟨(b63e_holForm_finrank_homeomorph _ _ (b6m_coordinate b rfw_E t₀)).trans rfw_holForm_finrank,
    rf6_relForm_frame b rfw_E (b6t_polydisc b) subset_rfl (rf5_polydisc_isOpen b)
      (rfw_fibreCharts b) (fun t ↦ rfw_incl b t) (rfw_family b) t₀⟩

#check @b63e_relForm

end HodgeLean.Foundations.Program

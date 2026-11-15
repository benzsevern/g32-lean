import HodgeLean.Foundations.Program.RelativeFrameChartsProofs
import HodgeLean.Foundations.Program.PrymVariationFrames

/-! # Relative frames in atlas charts (C12) and the extension of fibre forms (D1): statement draft
Implications, for a plumbing datum of the whole family over `V ⊆ b6t_polydisc b` (`rf5_FamilyPlumbing`:
analytic moving values, a fibre plumbing datum at each parameter identified with the base by the
product coordinate, outer charts analytic on the total space, disc coordinates restricted from
analytic functions on the total space), with an analytic manifold structure on the total space and
holomorphic fibre inclusions: from an analytic parameter family of source data to joint analyticity
of the outer part of the glued form and of each sector form in every fibre-preserving atlas chart;
from a kernel element of `δ_ε` to agreement of the glued form with the sector form on each inner
piece; from an analytic family of kernel elements to an element of `b63e_relForm` (C12); and, with
compact connected fibres and `V` open, from a holomorphic form on one fibre to a relative form near
that parameter restricting to it (D1, the replacement of `b63e_relForm_extend`).

Not claimed: the construction of `rf5_FamilyPlumbing` for the B6-2b family, which is stage B on the
total space (B3–B10) and is neither supplied nor assumed here; the restated frame, filtration and
variation statements D2–D4 (planned in `docs/specs/RelativeFrameCharts.md`); stage E. HC no
distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- Outer part of C12: in every fibre-preserving atlas chart `φ` of the total space, the glued form
of an analytic family `e` of source data has, over the outer region `O`, a coefficient against the
vertical coordinate of `φ` that is analytic jointly in the parameter and the fibre coordinate. In a
piece `i` it is `α(s)_i(U_i(s, z)) ∂_z U_i(s, z)`, with `U_i(s, z)` the stationary coordinate of
`φ⁻¹(s, z)`; point evaluation of `α(s)` is analytic jointly (Osgood), and the pieces agree by the
compatibility of `rf2_bddForm`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.4 (coefficient in a stationary chart of
`O`); `b63r_eval_analytic`; Forster, *Lectures on Riemann Surfaces*, §9. -/
theorem rf5_outer_chart_analytic {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b}
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (F : rf5_FamilyPlumbing b C D V hV) (W : Set (Fin 10 → ℂ)) (hW : IsOpen W)
    (e : (Fin 10 → ℂ) → rf4_Src D) (he : AnalyticOnNhd ℂ e W)
    (φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hφ : φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hp : ∀ y ∈ φ.source, (φ y).1 = y.1.val) :
    ∃ a : (Fin 10 → ℂ) × ℂ → ℂ,
      AnalyticOn ℂ a (φ.target ∩ Prod.fst ⁻¹' (V ∩ W) ∩ φ.symm ⁻¹' {q | q.2 ∈ O}) ∧
      ∀ (t : V) (x : b63l_parameterFibre b C V hV t), t.val ∈ W → x.val ∈ φ.source →
        x.val.2 ∈ O → ∀ v : TangentSpace 𝓘(ℂ, ℂ) x,
          rf4_glue (F.S t) (e t.val) ⟨x, v⟩ = a (φ x.val) * (show ℂ from
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
              (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) x v) :=
  rf5_outer_chart_analytic_aux hincl F W hW e he φ hφ hp

example := @rf5_outer_chart_analytic

/-- Inner part of C12 (B8 on the total space): in every fibre-preserving atlas chart `φ`, the
sector form `n Σ_{j<n} wʲ g_j(s)(c + ε(s) + wⁿ) dw` of an analytic family has, over the moving
inner piece of disc `x₀`, a coefficient against the vertical coordinate of `φ` that is analytic
jointly. With `W_φ(s, z) = wTot x₀ (φ⁻¹(s, z))`, analytic because `wTot x₀` is, it is
`sectorCoeff(g(s))(c + ε(s), W_φ) ∂_z W_φ`; the argument `c + ε(s) + W_φⁿ` stays in `D(c, 2r)` on
the inner piece.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.4 (`w`-coefficient on `Δ_x`, `w_t` jointly
analytic in the atlas charts) and §4.1 item 2 (B8d); `b63r_eval_analytic`. -/
theorem rf5_sector_chart_analytic {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b}
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (F : rf5_FamilyPlumbing b C D V hV) (W : Set (Fin 10 → ℂ)) (hW : IsOpen W)
    (e : (Fin 10 → ℂ) → rf4_Src D) (he : AnalyticOnNhd ℂ e W)
    (φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hφ : φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hp : ∀ y ∈ φ.source, (φ y).1 = y.1.val) (x₀ : Fin D.m) :
    ∃ a : (Fin 10 → ℂ) × ℂ → ℂ,
      AnalyticOn ℂ a (φ.target ∩ Prod.fst ⁻¹' (V ∩ W) ∩ {p | φ.symm p ∈ F.wSrc x₀ ∧
        F.wTot x₀ (φ.symm p) ∈ rf4_innerDisc (D.deg x₀) D.r (F.ε p.1 x₀)}) ∧
      ∀ (t : V) (y : b63l_parameterFibre b C V hV t), t.val ∈ W → y.val ∈ φ.source →
        y ∈ ((F.S t).w x₀).source →
        (F.S t).w x₀ y ∈ rf4_innerDisc (D.deg x₀) D.r (F.ε t x₀) →
        ∀ v : TangentSpace 𝓘(ℂ, ℂ) y,
          rf5_sectorForm (F.S t) (e t.val) x₀ ⟨y, v⟩ = a (φ y.val) * (show ℂ from
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
              (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) y v) :=
  rf5_sector_chart_analytic_aux hincl F W hW e he φ hφ hp x₀

example := @rf5_sector_chart_analytic

/-- Agreement on the inner pieces: for a kernel element of `δ_ε`, the glued form equals the sector
form at every point of the inner piece of disc `x`. Off `O` the glued form is the sector form of
the unique disc containing the point (`disjoint`). On the overlap, which is the annulus piece
(`overlap`), `w = Φ_ε(u)` (`glue`), and the differential pullback
`Φ_εʲ Φ_ε' = uʲ (1 − εu⁻ⁿ)^{s_j}` with `Φ_εⁿ = uⁿ − ε` turns the sector form into
`(S(ε) g)(u) du`, which is the outer coefficient `α_x(u) du` because `δ_ε(α, g) = 0`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.2 (differential pullback, kernel) and §5,
C3; Ahlfors, *Complex Analysis*, 3rd ed., Ch. 3, §4. -/
theorem rf5_glue_eq_sector {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : rf4_Src D) (hk : k ∈ (rf4_delta D ε).ker) (x : Fin D.m)
    (y : X) (hy : y ∈ (S.w x).source) (hyD : S.w x y ∈ rf4_innerDisc (D.deg x) D.r (ε x))
    (v : TangentSpace 𝓘(ℂ, ℂ) y) :
    rf4_glue S k ⟨y, v⟩ = rf5_sectorForm S k x ⟨y, v⟩ :=
  rf5_glue_eq_sector_aux S k hk x y hy hyD v

example := @rf5_glue_eq_sector

/-- C12: an analytic family of kernel elements of `δ_{ε(t)}` over an open `W` glues to a relative
holomorphic differential over `V ∩ W`. Fibrewise holomorphy is `rf4_kernel_equiv`. In a
fibre-preserving chart the coefficient is the outer coefficient of `rf5_outer_chart_analytic` over
`O` and the sector coefficient of `rf5_sector_chart_analytic` over each inner piece; the two agree
where both apply, by `rf5_glue_eq_sector` and because the vertical coordinate of `φ` restricts to a
local coordinate of each fibre (an injective holomorphic function). The fibres are covered by `O`
and the inner pieces (`cover`).
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.4 and §5, C12; Griffiths, *Periods of
integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968), §1. -/
theorem rf5_relForm_of_kernel {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b}
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (F : rf5_FamilyPlumbing b C D V hV) (W : Set (Fin 10 → ℂ)) (hW : IsOpen W)
    (e : (Fin 10 → ℂ) → rf4_Src D) (he : AnalyticOnNhd ℂ e W)
    (hk : ∀ t : V, t.val ∈ W → e t.val ∈ (rf4_delta D (F.ε t)).ker) :
    rf5_relGlue F W e ∈ b63e_relForm b C V hV W :=
  rf5_relForm_of_kernel_aux hincl F W hW e he hk

example := @rf5_relForm_of_kernel

/-- D1, the replacement of `b63e_relForm_extend`: over an open `V` with compact connected fibres,
a holomorphic form `η` on the fibre at `t₀` is the fibre value at `t₀` of a relative form over a
neighbourhood `W ⊆ V` of `t₀`. The kernel frame A3 applies to `t ↦ δ_{ε(t)}` (analytic by C5,
Fredholm at `t₀` by C10, kernel dimension `g` everywhere by C7 and the homeomorphism invariance of
the genus); the extension is C12 applied to `Σ_k c_k e_k(t)`, where `c` are the coordinates of the
kernel element of `η` in the frame at `t₀`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.4 (extension of an arbitrary `η`) and §5,
D1; `b63r_analytic_kernel_frame`, `rf4_delta_analytic`, `rf4_delta_isFredholm`, `rf4_ker_finrank`,
`rf4_kernel_equiv`, `b63e_holForm_finrank_homeomorph`. -/
theorem rf5_relForm_extend {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b} (hVo : IsOpen V)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (F : rf5_FamilyPlumbing b C D V hV) (t₀ : V)
    (η : b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀)) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
      ∃ θ : b63e_relForm b C V hV W, b63e_relFormAt b C V hV θ t₀ = η :=
  rf5_relForm_extend_aux hVo hincl F t₀ η

example := @rf5_relForm_extend

/-! ## Chain check

The Lean field this stage serves is `b63e_relForm` and, through it, the conclusion of the set-aside
`b63e_relForm_frame` (D2). The structural proof of `b63e_relForm_frame` used only the helper
`b63e_relForm_extend`, `b63e_relForm_mono`, `b63e_relForm_independent_near` and
`b63e_holForm_finrank_homeomorph`. With `rf5_relForm_extend` in place of the helper, and the family
plumbing datum in addition to the frozen premises, the same proof gives the frozen conclusion. -/

set_option maxHeartbeats 400000 in
example {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b} (hVo : IsOpen V)
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
    (F : rf5_FamilyPlumbing b C D V hV) (t₀ : V) :
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

/-- C12 feeds the period field: the periods of the relative form of `rf5_relForm_extend` on
transported integral classes are analytic, by the checked `b63e_period_analytic`. -/
example {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b} (hVo : IsOpen V)
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
    (F : rf5_FamilyPlumbing b C D V hV) (t₀ : V)
    (η : b3_HolForm ℂ (b63l_parameterFibre b C V hV t₀))
    (x : b6m_H1 (b63l_parameterFibre b C V hV t₀)) :
    ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀.val ∈ W ∧ W ⊆ V ∧
      ∃ θ : b63e_relForm b C V hV W, b63e_relFormAt b C V hV θ t₀ = η ∧
        AnalyticOnNhd ℂ (b63e_periodFunction b C V hV P θ t₀ x) (V ∩ W) := by
  obtain ⟨W, hW, htW, hWV, θ, hθ⟩ := rf5_relForm_extend hVo hincl F t₀ η
  exact ⟨W, hW, htW, hWV, θ, hθ, b63e_period_analytic b C V hV hVo hA hincl P hP W hW θ t₀ x⟩

#check @b63e_relForm

/-! ## Satisfiable instances, non-degenerate

A family over the whole polydisc of any `b`, with base surface the sphere: the total space
`b6t_polydisc b × OnePoint ℂ` with its product charts, each fibre charted by the sphere charts
through its product coordinate, outer data with one disc of degree one, and the moving value
`ε(t) = t₀ − b₀`, which is nonzero at some parameter. Every check uses definitions and checked
results only, never a statement of this file. -/

section SphereFamily

/-- The polydisc is open.
Source: the finite product topology; `b6t_polydisc`. -/
theorem rf5_polydisc_isOpen (b : Fin 10 → ℂ) : IsOpen (b6t_polydisc b) := by
  have : b6t_polydisc b = Set.pi univ (fun i ↦ Metric.ball (b i) (b6t_radius b)) := by
    ext t; simp [b6t_polydisc, Set.mem_pi]
  rw [this]
  exact isOpen_set_pi finite_univ (fun _ _ ↦ Metric.isOpen_ball)

/-- The polydisc as an open set.
Source: Mathlib `TopologicalSpace.Opens`; `b6t_polydisc`. -/
def rf5_polydiscOpens (b : Fin 10 → ℂ) : TopologicalSpace.Opens (Fin 10 → ℂ) :=
  ⟨b6t_polydisc b, rf5_polydisc_isOpen b⟩

/-- Charts of the polydisc, as an open subset of `ℂ¹⁰`.
Source: Mathlib, the charted space of an open subset. -/
@[instance_reducible] def rf5_polydiscCharted (b : Fin 10 → ℂ) :
    ChartedSpace (Fin 10 → ℂ) (b6t_polydisc b) :=
  inferInstanceAs (ChartedSpace (Fin 10 → ℂ) (rf5_polydiscOpens b))

attribute [local instance] rf5_polydiscCharted b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The polydisc is an analytic manifold.
Source: Mathlib, open subsets of manifolds. -/
theorem rf5_polydisc_isManifold (b : Fin 10 → ℂ) :
    IsManifold 𝓘(ℂ, Fin 10 → ℂ) ω (b6t_polydisc b) :=
  inferInstanceAs (IsManifold 𝓘(ℂ, Fin 10 → ℂ) ω (rf5_polydiscOpens b))

attribute [local instance] rf5_polydisc_isManifold

/-- Product charts of the total space over the sphere.
Source: Mathlib `prodChartedSpace`; `b4cov_sphChartedSpace`. -/
@[instance_reducible] def rf5_totalCharted (b : Fin 10 → ℂ) :
    ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × OnePoint ℂ) :=
  prodChartedSpace (Fin 10 → ℂ) (b6t_polydisc b) ℂ (OnePoint ℂ)

attribute [local instance] rf5_totalCharted

/-- The total space over the sphere is an analytic manifold.
Source: Mathlib `IsManifold.prod`; `b4cov_sph_isManifold`. -/
theorem rf5_total_isManifold (b : Fin 10 → ℂ) :
    IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × OnePoint ℂ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℂ, Fin 10 → ℂ)) (I' := 𝓘(ℂ, ℂ)) (b6t_polydisc b) (OnePoint ℂ)


/-! ## Fibres with the structure of the sphere -/

/-- The product coordinate of a fibre, as a single chart onto the sphere.
Source: `b6m_coordinate`. -/
def rf5_fibreChart (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    OpenPartialHomeomorph (b6m_Fibre b (OnePoint ℂ) t) (OnePoint ℂ) :=
  (b6m_coordinate b (OnePoint ℂ) t).toOpenPartialHomeomorph

/-- The fibre charted over the sphere by its coordinate.
Source: Mathlib `OpenPartialHomeomorph.singletonChartedSpace`. -/
@[instance_reducible] def rf5_fibreSph (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    ChartedSpace (OnePoint ℂ) (b6m_Fibre b (OnePoint ℂ) t) :=
  (rf5_fibreChart b t).singletonChartedSpace (by simp [rf5_fibreChart])

/-- The fibre charted over `ℂ`: the sphere charts composed with the coordinate.
Source: Mathlib `ChartedSpace.comp`; `b4cov_sphChartedSpace`. -/
@[instance_reducible] def rf5_fibreCharted (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    ChartedSpace ℂ (b6m_Fibre b (OnePoint ℂ) t) :=
  @ChartedSpace.comp ℂ _ (OnePoint ℂ) _ (b6m_Fibre b (OnePoint ℂ) t) _ _ (rf5_fibreSph b t)

/-- Composing two charts with a homeomorphism does not change their transition. -/
theorem rf5_comp_transition {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (c : X ≃ₜ Y)
    (f f' : OpenPartialHomeomorph Y ℂ) :
    (c.toOpenPartialHomeomorph ≫ₕ f).symm ≫ₕ (c.toOpenPartialHomeomorph ≫ₕ f') ≈ f.symm ≫ₕ f' := by
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc c.toOpenPartialHomeomorph.symm]
  have h1 : c.toOpenPartialHomeomorph.symm ≫ₕ c.toOpenPartialHomeomorph ≈
      OpenPartialHomeomorph.refl Y := by
    have := OpenPartialHomeomorph.symm_trans_self c.toOpenPartialHomeomorph
    simp only [Homeomorph.toOpenPartialHomeomorph_target] at this
    rwa [OpenPartialHomeomorph.ofSet_univ_eq_refl] at this
  have h2 := OpenPartialHomeomorph.EqOnSource.trans' (Setoid.refl f.symm)
    (OpenPartialHomeomorph.EqOnSource.trans' h1 (Setoid.refl f'))
  rwa [OpenPartialHomeomorph.refl_trans] at h2

/-- Each fibre of the sphere family is a Riemann surface.
Source: the transitions are those of the sphere, `b4cov_sph_isManifold`. -/
theorem rf5_fibre_isManifold (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    @IsManifold ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ω (b6m_Fibre b (OnePoint ℂ) t) _ (rf5_fibreCharted b t) := by
  let _ := rf5_fibreCharted b t
  refine { compatible := ?_ }
  rintro _ _ ⟨c, hc, f, hf, rfl⟩ ⟨c', hc', f', hf', rfl⟩
  have hc1 : c = rf5_fibreChart b t := hc
  have hc2 : c' = rf5_fibreChart b t := hc'
  subst hc1 hc2
  exact (contDiffGroupoid ω 𝓘(ℂ, ℂ)).mem_of_eqOnSource
    (HasGroupoid.compatible hf hf') (rf5_comp_transition _ f f')

/-- A sphere chart composed with the coordinate is a chart of the fibre. -/
theorem rf5_fibre_mem_maximalAtlas (b : Fin 10 → ℂ) (t : b6t_polydisc b)
    {f : OpenPartialHomeomorph (OnePoint ℂ) ℂ}
    (hf : f ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (OnePoint ℂ)) :
    rf5_fibreChart b t ≫ₕ f ∈ @IsManifold.maximalAtlas ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ω
      (b6m_Fibre b (OnePoint ℂ) t) _ (rf5_fibreCharted b t) := by
  let _ := rf5_fibreCharted b t
  rintro _ ⟨c, hc, f', hf', rfl⟩
  have hc1 : c = rf5_fibreChart b t := hc
  subst hc1
  exact ⟨(contDiffGroupoid ω 𝓘(ℂ, ℂ)).mem_of_eqOnSource (hf f' hf').1
      (rf5_comp_transition _ f f'),
    (contDiffGroupoid ω 𝓘(ℂ, ℂ)).mem_of_eqOnSource (hf f' hf').2
      (rf5_comp_transition _ f' f)⟩


/-- Transport of a plumbing datum along a homeomorphism `c : X ≃ₜ Y` that carries the charts of
`Y` to charts of `X`.
Source: the definition `rf4_Plumbing`; images of sets under a homeomorphism. -/
def rf5_transportPlumbing {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] (c : X ≃ₜ Y)
    (hc : ∀ f ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω Y,
      c.toOpenPartialHomeomorph ≫ₕ f ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (P : rf4_Plumbing D ε Y) : rf4_Plumbing D ε X where
  h := P.h.trans c.symm
  stationary i := by
    have := hc _ (P.stationary i)
    rwa [← OpenPartialHomeomorph.trans_assoc, ← Homeomorph.trans_toOpenPartialHomeomorph] at this
  small := P.small
  w x := c.toOpenPartialHomeomorph ≫ₕ P.w x
  w_mem x := hc _ (P.w_mem x)
  w_target x := by
    simpa [OpenPartialHomeomorph.trans_target] using P.w_target x
  cover p := by
    rcases P.cover (c p) with h | ⟨x, hx⟩
    · exact Or.inl (by simpa using h)
    · refine Or.inr ⟨x, ?_⟩
      obtain ⟨v, hv, hve⟩ := hx
      exact ⟨v, hv, by simp [hve]⟩
  disjoint x y hxy := by
    have h := (P.disjoint hxy).image (f := c.symm) c.symm.injective.injOn
      (subset_univ _) (subset_univ _)
    simpa [image_image] using h
  overlap x := by
    have h := congrArg (fun s ↦ c.symm '' s) (P.overlap x)
    simp only [image_inter c.symm.injective] at h
    simp only [image_image] at h
    convert h using 3
    · rfl
    · rfl
    · rw [image_image]; rfl
  glue x u hu := by
    obtain ⟨h1, h2⟩ := P.glue x u hu
    exact ⟨by simpa using h1, by simpa using h2⟩


attribute [local instance] rf5_fibreCharted rf5_fibre_isManifold

/-- The radius of the polydisc is at most `1/4`. -/
theorem rf5_radius_le (b : Fin 10 → ℂ) : b6t_radius b ≤ 1 / 4 := by
  unfold b6t_radius
  have hS : 0 ≤ ∑ i : Fin 10, (‖b i‖⁻¹ + ‖b i - 1‖⁻¹ +
      ∑ j : Fin 10, if i = j then 0 else (dist (b i) (b j))⁻¹) := by
    refine Finset.sum_nonneg fun i _ ↦ add_nonneg (by positivity)
      (Finset.sum_nonneg fun j _ ↦ ?_)
    split_ifs <;> positivity
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

/-- The moving value of the sphere family: `ε(t) = t₀ − b₀`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 (`ε_i = t_i − b_i`). -/
def rf5_sphereEps (b : Fin 10 → ℂ) : (Fin 10 → ℂ) → Fin 1 → ℂ := fun s _ ↦ s 0 - b 0

/-- The moving value is smaller than the radius one of the sphere outer data. -/
theorem rf5_sphereEps_small (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    ‖t.val 0 - b 0‖ < 1 := by
  have h := t.property 0
  rw [Metric.mem_ball, dist_eq_norm] at h
  linarith [rf5_radius_le b]

/-- The plumbing datum of the fibre at `t` of the sphere family, transported from the sphere.
Source: `rf4_spherePlumbing`. -/
def rf5_spherePlumbingAt (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    rf4_Plumbing (rf4_sphereOuter 1 le_rfl) (rf5_sphereEps b t) (b6m_Fibre b (OnePoint ℂ) t) :=
  rf5_transportPlumbing (b6m_coordinate b (OnePoint ℂ) t)
    (fun _ hf ↦ rf5_fibre_mem_maximalAtlas b t hf)
    (rf4_spherePlumbing 1 le_rfl (t.val 0 - b 0) (rf5_sphereEps_small b t) (Or.inl rfl))

/-- The sphere family: one disc of degree one around `0`, moving value `t₀ − b₀`, over the whole
polydisc.
Source: `rf4_sphereOuter`, `rf4_spherePlumbing`; RelativeFrame §4.1. -/
def rf5_sphereFamily (b : Fin 10 → ℂ) :
    rf5_FamilyPlumbing b (OnePoint ℂ) (rf4_sphereOuter 1 le_rfl) (b6t_polydisc b) subset_rfl where
  ε := rf5_sphereEps b
  ε_analytic := by
    intro s _
    exact AnalyticAt.pi fun _ ↦ ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 10 ↦ ℂ) 0).analyticAt s).sub analyticAt_const
  S t := rf5_spherePlumbingAt b t
  h_eq t := by ext; rfl
  outer_analytic i := by
    rw [modelWithCornersSelf_prod]
    exact (contMDiffOn_of_mem_maximalAtlas ((rf4_sphereCover 1 le_rfl).analytic i)).comp
      contMDiff_snd.contMDiffOn (fun q hq ↦ hq)
  wTot _ q := b4cov_chart0 q.2 - (q.1.val 0 - b 0)
  wSrc _ := {q | q.2 ∈ b4cov_chart0.source}
  wSrc_open _ := b4cov_chart0.open_source.preimage continuous_snd
  w_analytic _ := by
    rw [modelWithCornersSelf_prod]
    have h1 : ContMDiffOn (𝓘(ℂ, Fin 10 → ℂ).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, ℂ) ω
        (fun q : b6t_polydisc b × OnePoint ℂ ↦ b4cov_chart0 q.2)
        {q | q.2 ∈ b4cov_chart0.source} :=
      (contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (Or.inl rfl))).comp
        contMDiff_snd.contMDiffOn (fun q hq ↦ hq)
    have h2 : ContMDiff (𝓘(ℂ, Fin 10 → ℂ).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, ℂ) ω
        (fun q : b6t_polydisc b × OnePoint ℂ ↦ q.1.val 0 - b 0) := by
      have hv : ContMDiff 𝓘(ℂ, Fin 10 → ℂ) 𝓘(ℂ, Fin 10 → ℂ) ω
          (fun s : b6t_polydisc b ↦ s.val) :=
        contMDiff_subtype_val (U := rf5_polydiscOpens b)
      have he : ContMDiff 𝓘(ℂ, Fin 10 → ℂ) 𝓘(ℂ, ℂ) ω (fun s : Fin 10 → ℂ ↦ s 0 - b 0) :=
        (by fun_prop : ContDiff ℂ ω (fun s : Fin 10 → ℂ ↦ s 0 - b 0)).contMDiff
      exact (he.comp hv).comp contMDiff_fst
    exact h1.sub h2.contMDiffOn
  w_source t _ y := by
    simp [rf5_spherePlumbingAt, rf5_transportPlumbing, rf4_spherePlumbing,
      rf4_sphereDisc_source, b6m_coordinate]
    exact Iff.rfl
  w_eq t _ y _ := by
    simp [rf5_spherePlumbingAt, rf5_transportPlumbing, rf4_spherePlumbing, rf4_sphereDisc,
      b6m_coordinate, sub_eq_add_neg, y.property]
    rfl


/-- The fibre coordinate is holomorphic for the transported structure. -/
theorem rf5_coordinate_contMDiff (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b6m_coordinate b (OnePoint ℂ) t) := by
  intro y
  let f := chartAt ℂ (b6m_coordinate b (OnePoint ℂ) t y)
  have hf : f ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (OnePoint ℂ) :=
    IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ _)
  have hg := rf5_fibre_mem_maximalAtlas b t hf
  have hy : y ∈ (rf5_fibreChart b t ≫ₕ f).source := by
    simp [rf5_fibreChart, f, mem_chart_source]
  have h := ((contMDiffOn_symm_of_mem_maximalAtlas hf).comp
    (contMDiffOn_of_mem_maximalAtlas hg) (fun z hz ↦ ((rf5_fibreChart b t ≫ₕ f).map_source hz).1)
    ).contMDiffAt ((rf5_fibreChart b t ≫ₕ f).open_source.mem_nhds hy)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(rf5_fibreChart b t ≫ₕ f).open_source.mem_nhds hy] with z hz
  have hz' : b6m_coordinate b (OnePoint ℂ) t z ∈ f.source := by
    simpa [rf5_fibreChart] using hz.2
  simp [rf5_fibreChart, f.left_inv hz']

/-- The fibre inclusions of the sphere family are holomorphic. -/
theorem rf5_sphere_incl (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b6m_Fibre b (OnePoint ℂ) t ↦ x.val) := by
  have he : (fun x : b6m_Fibre b (OnePoint ℂ) t ↦ x.val) =
      fun x ↦ (t, b6m_coordinate b (OnePoint ℂ) t x) := by
    funext x
    exact Prod.ext x.property rfl
  rw [he, modelWithCornersSelf_prod]
  exact contMDiff_const.prodMk (rf5_coordinate_contMDiff b t)

/-- Fibres of the sphere family are Hausdorff. -/
instance rf5_fibre_t2 (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    T2Space (b6m_Fibre b (OnePoint ℂ) t) :=
  (b6m_coordinate b (OnePoint ℂ) t).isEmbedding.t2Space

/-- Fibres of the sphere family are compact. -/
instance rf5_fibre_compact (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    CompactSpace (b6m_Fibre b (OnePoint ℂ) t) :=
  (b6m_coordinate b (OnePoint ℂ) t).symm.compactSpace

/-- Fibres of the sphere family are connected. -/
instance rf5_fibre_connected (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    ConnectedSpace (b6m_Fibre b (OnePoint ℂ) t) :=
  (b6m_coordinate b (OnePoint ℂ) t).symm.surjective.connectedSpace
    (b6m_coordinate b (OnePoint ℂ) t).symm.continuous

/-- Every point of the total space lies in a fibre-preserving product chart. -/
theorem rf5_sphere_fibreCharts (b : Fin 10 → ℂ) (q : b6t_polydisc b × OnePoint ℂ) :
    ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × OnePoint ℂ),
      q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val :=
  ⟨chartAt _ q, chart_mem_atlas _ q, mem_chart_source _ q, fun y _ ↦ by
    rfl⟩

/-- A parameter of the polydisc with moving value `ε ≠ 0`. -/
theorem rf5_sphere_moving (b : Fin 10 → ℂ) :
    ∃ t : b6t_polydisc b, rf5_sphereEps b t.val ≠ 0 := by
  have hr : 0 < b6t_radius b := by
    unfold b6t_radius
    have hS : 0 ≤ ∑ i : Fin 10, (‖b i‖⁻¹ + ‖b i - 1‖⁻¹ +
        ∑ j : Fin 10, if i = j then 0 else (dist (b i) (b j))⁻¹) := by
      refine Finset.sum_nonneg fun i _ ↦ add_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ ↦ ?_)
      split_ifs <;> positivity
    positivity
  let t : Fin 10 → ℂ := Function.update b 0 (b 0 + (b6t_radius b / 2 : ℝ))
  have ht : t ∈ b6t_polydisc b := by
    intro i
    rw [Metric.mem_ball, dist_eq_norm]
    by_cases hi : i = 0
    · subst hi
      simp only [t, Function.update_self, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      linarith
    · simp [t, Function.update_of_ne hi, hr]
  refine ⟨⟨t, ht⟩, fun h ↦ ?_⟩
  have := congrFun h 0
  simp only [rf5_sphereEps, t, Function.update_self, add_sub_cancel_left, Pi.zero_apply,
    Complex.ofReal_eq_zero] at this
  linarith


/-- The differential of a chart of a Riemann surface does not vanish. -/
theorem rf5_mfderiv_chart_ne_zero {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X) {y : X} (hy : y ∈ e.source) :
    (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e y (1 : ℂ)) ≠ 0 := by
  have h := isInvertible_mfderiv_extend (I := 𝓘(ℂ, ℂ))
    (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hy
  have hext : ((e.extend 𝓘(ℂ, ℂ) : X → ℂ)) = e := by
    funext z; simp
  rw [hext] at h
  intro h0
  obtain ⟨L, hL⟩ := h
  have h1 : L (1 : ℂ) = 0 := by
    rw [← ContinuousLinearEquiv.coe_coe, hL]; exact h0
  exact one_ne_zero (α := ℂ) (L.injective (h1.trans (map_zero L).symm))


/-- Sector data `g_0 = 1` on `D(0, 2)` for the one disc of the sphere outer data.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.2 (sector map). -/
def rf5_testDisc : rf4_Disc (rf4_sphereOuter 1 le_rfl) := fun _ _ ↦
  ⟨BoundedContinuousFunction.const _ 1, ⟨fun _ ↦ 1, differentiableOn_const 1, fun _ ↦ rfl⟩⟩

/-- The sector form of the constant family `(0, g)`, `g_0 = 1`, is nonzero on a fibre with
moving value `ε ≠ 0`: at the point over `z = 0` it is `dw` with `w = z − ε`. -/
example (b : Fin 10 → ℂ) : ∃ t : b6t_polydisc b, rf5_sphereEps b t.val ≠ 0 ∧
    ∃ (y : b63l_parameterFibre b (OnePoint ℂ) (b6t_polydisc b) subset_rfl t)
      (v : TangentSpace 𝓘(ℂ, ℂ) y),
      rf5_sectorForm ((rf5_sphereFamily b).S t) (0, rf5_testDisc) ⟨0, Nat.one_pos⟩ ⟨y, v⟩ ≠ 0 := by
  obtain ⟨t, ht⟩ := rf5_sphere_moving b
  let y : b63l_parameterFibre b (OnePoint ℂ) (b6t_polydisc b) subset_rfl t :=
    ⟨(t, ((0 : ℂ) : OnePoint ℂ)), rfl⟩
  refine ⟨t, ht, y, (1 : ℂ), ?_⟩
  have hy : y ∈ (((rf5_sphereFamily b).S t).w ⟨0, Nat.one_pos⟩).source := by
    refine ((rf5_sphereFamily b).w_source t _ y).mpr ?_
    change ((0 : ℂ) : OnePoint ℂ) ∈ b4cov_chart0.source
    rw [b4cov_chart0_source]
    exact mem_range_self _
  refine mul_ne_zero ?_
    (rf5_mfderiv_chart_ne_zero (((rf5_sphereFamily b).S t).w_mem ⟨0, Nat.one_pos⟩) hy)
  have hw : ((rf5_sphereFamily b).S t).w ⟨0, Nat.one_pos⟩ y = -(t.val 0 - b 0) := by
    rw [(rf5_sphereFamily b).w_eq t ⟨0, Nat.one_pos⟩ y hy]
    change b4cov_chart0 ((0 : ℂ) : OnePoint ℂ) - (t.val 0 - b 0) = _
    rw [b4cov_chart0_coe, zero_sub]
  change rf4_sectorCoeff 1 (fun j ↦ rf4_extendBdd (rf5_testDisc ⟨0, Nat.one_pos⟩ j))
    (0 + (t.val 0 - b 0)) (((rf5_sphereFamily b).S t).w ⟨0, Nat.one_pos⟩ y) ≠ 0
  rw [hw]
  simp [rf4_sectorCoeff, rf4_extendBdd, rf5_testDisc]
  change ‖(0 : ℂ)‖ < 2 * 1
  norm_num


/-- The coefficient `−1/z²` of `−dz/z² = d(1/z)` on the annulus piece.
Source: Forster, *Lectures on Riemann Surfaces*, §9. -/
def rf5_outerCoeff0 : b63r_bddHol (b63r_annulus 1 1) :=
  rf4_bddOn (rf4_closedAnnulus_isCompact le_rfl 1) (rf4_annulus_subset_closed 1 1)
    (fun z ↦ -(z ^ 2)⁻¹)
    (fun _ hz ↦ ((continuous_pow 2).continuousAt.inv₀
      (pow_ne_zero 2 (rf4_closedAnnulus_ne_zero le_rfl one_pos hz))).neg.continuousWithinAt)
    (fun z hz ↦ (((differentiableAt_pow (𝕜 := ℂ) (x := z) 2)).inv (pow_ne_zero 2
      (rf4_closedAnnulus_ne_zero le_rfl one_pos (rf4_annulus_subset_closed 1 1 hz)))).neg
      |>.differentiableWithinAt)

/-- The constant coefficient `1` of `dv`, `v = 1/z`, on the disc around `∞`.
Source: Forster, *Lectures on Riemann Surfaces*, §9. -/
def rf5_outerCoeff1 : b63r_bddHol (Metric.ball (0 : ℂ) 1) :=
  ⟨BoundedContinuousFunction.const _ 1, ⟨fun _ ↦ 1, differentiableOn_const 1, fun _ ↦ rfl⟩⟩

/-- The transition of `z` with itself. -/
theorem rf5_chart00 : (b4cov_chart0 ∘ b4cov_chart0.symm : ℂ → ℂ) = id := by
  funext z; simp [b4cov_chart0_symm, b4cov_chart0_coe]

/-- The transition of `1/z` with itself. -/
theorem rf5_chart11 : (b4cov_chartInf ∘ b4cov_chartInf.symm : ℂ → ℂ) = id := by
  funext v
  simp only [Function.comp_apply, b4cov_chartInf_symm, b4cov_chartInf_apply,
    b4cov_sphInv_involutive _, b4cov_chart0_coe, id]

/-- The transition from `z` to `1/z`. -/
theorem rf5_chart01 {z : ℂ} (hz : z ≠ 0) :
    (b4cov_chartInf ∘ b4cov_chart0.symm : ℂ → ℂ) =ᶠ[𝓝 z] fun u ↦ u⁻¹ := by
  filter_upwards [isOpen_ne.mem_nhds hz] with u hu
  simp only [Function.comp_apply, b4cov_chart0_symm, b4cov_chartInf_apply]
  exact b4cov_chart0_sphInv hu

/-- The transition from `1/z` to `z`. -/
theorem rf5_chart10 {v : ℂ} (hv : v ≠ 0) :
    (b4cov_chart0 ∘ b4cov_chartInf.symm : ℂ → ℂ) =ᶠ[𝓝 v] fun u ↦ u⁻¹ := by
  filter_upwards [isOpen_ne.mem_nhds hv] with u hu
  simp only [Function.comp_apply, b4cov_chartInf_symm]
  exact b4cov_chart0_sphInv hu

/-- The form `d(1/z)` on the outer region of the sphere, as a bounded chart form: `−1/z²` on the
annulus piece and `1` on the disc around `∞`.
Source: Forster, *Lectures on Riemann Surfaces*, §9; RelativeFrame §5, A14. -/
def rf5_outerForm : rf2_bddForm (rf4_sphereCover 1 le_rfl) :=
  ⟨fun i ↦ Fin.cases (motive := fun i ↦ b63r_bddHol (rf4_spherePieces 1 i)) rf5_outerCoeff0
    (fun j ↦ Fin.cases (motive := fun j ↦ b63r_bddHol (rf4_spherePieces 1 j.succ))
      rf5_outerCoeff1 (fun k ↦ k.elim0) j) i, by
    intro i j z w h
    obtain ⟨z, hz⟩ := z
    obtain ⟨w, hw⟩ := w
    fin_cases i <;> fin_cases j
    · change b4cov_chart0.symm z = b4cov_chart0.symm w at h
      change -(z ^ 2)⁻¹ = -(w ^ 2)⁻¹ * deriv (b4cov_chart0 ∘ b4cov_chart0.symm) z
      rw [b4cov_chart0_symm, b4cov_chart0_symm] at h
      cases OnePoint.coe_injective h
      rw [rf5_chart00, deriv_id, mul_one]
    · change b4cov_chart0.symm z = b4cov_chartInf.symm w at h
      change -(z ^ 2)⁻¹ = 1 * deriv (b4cov_chartInf ∘ b4cov_chart0.symm) z
      have hz0 : z ≠ 0 := rf4_closedAnnulus_ne_zero le_rfl one_pos (rf4_annulus_subset_closed 1 1 hz)
      rw [(rf5_chart01 hz0).deriv_eq, deriv_inv, one_mul]
    · change b4cov_chartInf.symm z = b4cov_chart0.symm w at h
      change (1 : ℂ) = -(w ^ 2)⁻¹ * deriv (b4cov_chart0 ∘ b4cov_chartInf.symm) z
      rw [b4cov_chartInf_symm, b4cov_chart0_symm] at h
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [b4cov_sphInv_zero] at h
        exact OnePoint.infty_ne_coe w h
      rw [b4cov_sphInv_coe hz0] at h
      cases OnePoint.coe_injective h
      rw [(rf5_chart10 hz0).deriv_eq, deriv_inv]
      field_simp
    · change b4cov_chartInf.symm z = b4cov_chartInf.symm w at h
      change (1 : ℂ) = 1 * deriv (b4cov_chartInf ∘ b4cov_chartInf.symm) z
      rw [rf5_chart11, deriv_id, mul_one]⟩


/-- The glued form of the constant family `(d(1/z), 0)` is nonzero on a fibre with moving value
`ε ≠ 0`, at the point over `z = 3/2` of the outer region. -/
example (b : Fin 10 → ℂ) : ∃ t : b6t_polydisc b, rf5_sphereEps b t.val ≠ 0 ∧
    ∃ (y : b63l_parameterFibre b (OnePoint ℂ) (b6t_polydisc b) subset_rfl t)
      (v : TangentSpace 𝓘(ℂ, ℂ) y),
      rf4_glue ((rf5_sphereFamily b).S t) (rf5_outerForm, 0) ⟨y, v⟩ ≠ 0 := by
  obtain ⟨t, ht⟩ := rf5_sphere_moving b
  let y : b63l_parameterFibre b (OnePoint ℂ) (b6t_polydisc b) subset_rfl t :=
    ⟨(t, ((3 / 2 : ℂ) : OnePoint ℂ)), rfl⟩
  refine ⟨t, ht, y, (1 : ℂ), ?_⟩
  have hhy : ((rf5_sphereFamily b).S t).h.symm y = ((3 / 2 : ℂ) : OnePoint ℂ) := rfl
  have hO : ∃ i, ((rf5_sphereFamily b).S t).h.symm y ∈
      ((rf4_sphereOuter 1 le_rfl).P.chart i).source ∧
      (rf4_sphereOuter 1 le_rfl).P.chart i (((rf5_sphereFamily b).S t).h.symm y) ∈
        (rf4_sphereOuter 1 le_rfl).P.piece i := by
    refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · rw [hhy]
      change ((3 / 2 : ℂ) : OnePoint ℂ) ∈ b4cov_chart0.source
      rw [b4cov_chart0_source]
      exact mem_range_self _
    · rw [hhy]
      change b4cov_chart0 ((3 / 2 : ℂ) : OnePoint ℂ) ∈ b63r_annulus 1 1
      rw [b4cov_chart0_coe]
      constructor <;> norm_num [Complex.norm_div]
  unfold rf4_glue
  rw [dite_eq_left_of_eq_true (eq_true hO)]
  have hspec := Classical.choose_spec hO
  generalize Classical.choose hO = i at hspec ⊢
  refine mul_ne_zero ?_ ?_
  · rw [rf4_extendBdd, dite_eq_left_of_eq_true (eq_true hspec.2)]
    fin_cases i
    · change -((b4cov_chart0 ((3 / 2 : ℂ) : OnePoint ℂ)) ^ 2)⁻¹ ≠ 0
      rw [b4cov_chart0_coe]
      norm_num
    · change (1 : ℂ) ≠ 0
      exact one_ne_zero
  · have hm := ((rf5_sphereFamily b).S t).stationary i
    have hs : y ∈ (((rf5_sphereFamily b).S t).h.symm.toOpenPartialHomeomorph ≫ₕ
        (rf4_sphereOuter 1 le_rfl).P.chart i).source := by
      simpa using hspec.1
    exact rf5_mfderiv_chart_ne_zero hm hs


/-- The premises of every statement of this file hold for the sphere family: the total space is
an analytic manifold, the fibre inclusions are holomorphic, the fibres are compact, connected and
Hausdorff, every point lies in a fibre-preserving atlas chart (the premise `hA` of the chain
check), `V` is open, and the moving value is nonzero at some parameter. -/
example (b : Fin 10 → ℂ) :
    Nonempty (rf5_FamilyPlumbing b (OnePoint ℂ) (rf4_sphereOuter 1 le_rfl) (b6t_polydisc b)
      subset_rfl) ∧
    IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × OnePoint ℂ) ∧
    (∀ t : b6t_polydisc b, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b (OnePoint ℂ) (b6t_polydisc b) subset_rfl t ↦ x.val)) ∧
    (∀ t : b6t_polydisc b,
      T2Space (b63l_parameterFibre b (OnePoint ℂ) (b6t_polydisc b) subset_rfl t) ∧
      CompactSpace (b63l_parameterFibre b (OnePoint ℂ) (b6t_polydisc b) subset_rfl t) ∧
      ConnectedSpace (b63l_parameterFibre b (OnePoint ℂ) (b6t_polydisc b) subset_rfl t)) ∧
    (∀ q : b6t_polydisc b × OnePoint ℂ,
      ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × OnePoint ℂ),
        q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val) ∧
    IsOpen (b6t_polydisc b) ∧
    ∃ t : b6t_polydisc b, (rf5_sphereFamily b).ε t.val ≠ 0 :=
  ⟨⟨rf5_sphereFamily b⟩, rf5_total_isManifold b, fun t ↦ rf5_sphere_incl b t,
    fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩, rf5_sphere_fibreCharts b,
    rf5_polydisc_isOpen b, rf5_sphere_moving b⟩

/-- The source families of the two non-vanishing checks are analytic on the open polydisc, as
`rf5_outer_chart_analytic` and `rf5_sector_chart_analytic` require. -/
example (b : Fin 10 → ℂ) :
    AnalyticOnNhd ℂ (fun _ : Fin 10 → ℂ ↦ ((rf5_outerForm, 0) : rf4_Src (rf4_sphereOuter 1 le_rfl)))
      (b6t_polydisc b) ∧
    AnalyticOnNhd ℂ (fun _ : Fin 10 → ℂ ↦ ((0, rf5_testDisc) : rf4_Src (rf4_sphereOuter 1 le_rfl)))
      (b6t_polydisc b) :=
  ⟨analyticOnNhd_const, analyticOnNhd_const⟩

/-! ## Evaluations of the helper definitions -/

/-- The polydisc as an open set has the polydisc as carrier and contains its centre `b`. -/
example (b : Fin 10 → ℂ) :
    ((rf5_polydiscOpens b : Set (Fin 10 → ℂ)) = b6t_polydisc b) ∧ b ∈ rf5_polydiscOpens b := by
  refine ⟨rfl, fun i ↦ ?_⟩
  rw [Metric.mem_ball, dist_self]
  unfold b6t_radius
  have hS : 0 ≤ ∑ i : Fin 10, (‖b i‖⁻¹ + ‖b i - 1‖⁻¹ +
      ∑ j : Fin 10, if i = j then 0 else (dist (b i) (b j))⁻¹) := by
    refine Finset.sum_nonneg fun i _ ↦ add_nonneg (by positivity)
      (Finset.sum_nonneg fun j _ ↦ ?_)
    split_ifs <;> positivity
  positivity

/-- The chart of the polydisc at a parameter `t` sends `t` to its value in `ℂ¹⁰`. -/
example (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    chartAt (Fin 10 → ℂ) t t = t.val :=
  rfl

/-- The product chart of the total space at `(t, z)`, `z ∈ ℂ`, sends it to `(t, z)`. -/
example (b : Fin 10 → ℂ) (t : b6t_polydisc b) (z : ℂ) :
    chartAt ((Fin 10 → ℂ) × ℂ) (t, (z : OnePoint ℂ)) (t, (z : OnePoint ℂ)) = (t.val, z) := by
  change (t.val, b4cov_chart0 (z : OnePoint ℂ)) = (t.val, z)
  rw [b4cov_chart0_coe]

/-- The fibre chart is the product coordinate, defined on the whole fibre. -/
example (b : Fin 10 → ℂ) (t : b6t_polydisc b) (y : b6m_Fibre b (OnePoint ℂ) t) :
    rf5_fibreChart b t y = y.val.2 ∧ (rf5_fibreChart b t).source = univ :=
  ⟨rfl, by simp [rf5_fibreChart]⟩

/-- The fibre charted over the sphere has the fibre chart as its only chart. -/
example (b : Fin 10 → ℂ) (t : b6t_polydisc b) (y : b6m_Fibre b (OnePoint ℂ) t) :
    @chartAt (OnePoint ℂ) _ _ _ (rf5_fibreSph b t) y = rf5_fibreChart b t ∧
      @atlas (OnePoint ℂ) _ _ _ (rf5_fibreSph b t) = {rf5_fibreChart b t} :=
  ⟨rfl, rfl⟩

/-- The chart of a fibre at the point over `z ∈ ℂ` sends it to `z`. -/
example (b : Fin 10 → ℂ) (t : b6t_polydisc b) (z : ℂ) :
    let y : b6m_Fibre b (OnePoint ℂ) t := ⟨(t, (z : OnePoint ℂ)), rfl⟩
    @chartAt ℂ _ _ _ (rf5_fibreCharted b t) y y = z := by
  intro y
  change b4cov_chart0 (z : OnePoint ℂ) = z
  rw [b4cov_chart0_coe]

/-- Transport along the identity homeomorphism keeps the disc charts and the outer homeomorphism. -/
example {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C}
    {D : rf4_OuterData C O} {ε : Fin D.m → ℂ} {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (P : rf4_Plumbing D ε X) (x : Fin D.m) (p : X) :
    let Q := rf5_transportPlumbing (Homeomorph.refl X)
      (fun f hf ↦ by rwa [Homeomorph.refl_toOpenPartialHomeomorph,
        OpenPartialHomeomorph.refl_trans]) P
    Q.w x p = P.w x p ∧ Q.h.symm p = P.h.symm p :=
  ⟨rfl, rfl⟩

/-- The moving value at a parameter `s` is `s₀ − b₀`; it vanishes at the centre. -/
example (b s : Fin 10 → ℂ) (i : Fin 1) :
    rf5_sphereEps b s i = s 0 - b 0 ∧ rf5_sphereEps b b = 0 :=
  ⟨rfl, funext fun _ ↦ sub_self _⟩

/-- The plumbing datum at `t` identifies the outer region with the fibre by the product
coordinate, and its disc chart at the point over `z ∈ ℂ` takes the value `z − (t₀ − b₀)`. -/
example (b : Fin 10 → ℂ) (t : b6t_polydisc b) (z : ℂ) :
    let y : b6m_Fibre b (OnePoint ℂ) t := ⟨(t, (z : OnePoint ℂ)), rfl⟩
    (rf5_spherePlumbingAt b t).h.symm y = (z : OnePoint ℂ) ∧
      (rf5_spherePlumbingAt b t).w ⟨0, Nat.one_pos⟩ y = z - (t.val 0 - b 0) := by
  intro y
  refine ⟨rfl, ?_⟩
  change rf4_sphereDisc (t.val 0 - b 0) (z : OnePoint ℂ) = z - (t.val 0 - b 0)
  simp [rf4_sphereDisc, b4cov_chart0_coe, sub_eq_add_neg]

/-- The coefficient `−1/z²` at `z = 3/2` of the annulus piece is `−4/9`. -/
example : ((rf5_outerCoeff0 : b63r_bddHol (b63r_annulus 1 1)) : BoundedContinuousFunction (b63r_annulus 1 1) ℂ)
    ⟨3 / 2, by constructor <;> norm_num [b63r_annulus, Complex.norm_div]⟩ = -(4 / 9) := by
  change -(((3 / 2 : ℂ)) ^ 2)⁻¹ = -(4 / 9)
  norm_num

/-- The coefficient of `dv` on the disc around `∞` is `1` at `v = 0`. -/
example : ((rf5_outerCoeff1 : b63r_bddHol (Metric.ball (0 : ℂ) 1)) :
    BoundedContinuousFunction (Metric.ball (0 : ℂ) 1) ℂ) ⟨0, by simp⟩ = 1 := rfl

end SphereFamily

#print axioms rf5_sectorForm
#print axioms rf5_relGlue
#print axioms rf5_sphereFamily
#print axioms rf5_fibre_isManifold
#print axioms rf5_total_isManifold
#print axioms rf5_sphere_incl
#print axioms rf5_sphere_fibreCharts
#print axioms rf5_sphere_moving
#print axioms rf5_outerForm
#print axioms rf5_mfderiv_chart_ne_zero


end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.PeriodCoordinatesProofs
import HodgeLean.Papers.G32DominanceDefs

/-! # B6-4a: graph coordinates of the fixed bounded chart

The first stage of B6-4 (`docs/specs/PeriodCoordinates.md`). It concerns filtrations of
the fixed complexified Weil lattice `ℂ ⊗ ℤ[ω]⁶` of B6-0a and the explicit graph chart
`b60_F`, and claims:

* the graph coordinate `b64_graphCoord` inverts the negative frame of `b60_F`, and
  recovers the chart point from any three-frame spanning the same negative plane;
* a three-frame of the negative eigenspace with invertible head block spans the
  negative plane at its graph coordinate;
* the coordinate `b64_coordOf` reads off the chart point of `b60_F z` for every `z`;
* graph coordinates of frames with analytic eigen-coordinates and invertible head
  blocks are analytic;
* any spanning family of a family of chart filtrations has, near each parameter, three
  members whose negative parts frame the negative plane with invertible head block;
* the implication from analytic spanning families of chart filtrations on an open set
  to analyticity of `t ↦ b64_coordOf (F t)` on that set.

With `b60c_fixed_filtration_chart` this yields the `analytic` and `mapsTo` fields of
`g32r_PeriodMap` for `period := fun t => b64_coordOf (F t)` (the chain check at the end).
Nothing here constructs a filtration from a cover, a rational marking of a Prym lattice,
an isogeny, a Schlesinger path, a jet or a codifferential: those are later stages of
B6-4, B6-5 and B6-6. HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct Matrix Topology
open HodgeLean.Papers Filter Set
namespace HodgeLean.Foundations.Program

/-- The graph coordinate of the negative frame of `b60_F z` is `z`.
Source: van Geemen, LNM 1594, §5.10; `b60_frame`, `b60c_eigenBasis_apply`. -/
theorem b64_graphCoord_negFrame (z : Fin 9 → ℂ) :
    b64_graphCoord (b64_negFrame z) = z :=
  b64_graphCoord_negFrame_aux z

example : b64_graphCoord (b64_negFrame 0) = 0 := b64_graphCoord_negFrame 0

/-- The negative plane of `b60_F z` is spanned by its negative frame, for every `z`.
Source: van Geemen, LNM 1594, §§5.1, 5.10; `b60_frame`, `b60c_omega_eigenBasis`. -/
theorem b64_negFrame_span (z : Fin 9 → ℂ) :
    b60_F z ⊓ b64_Eminus = Submodule.span ℂ (Set.range (b64_negFrame z)) :=
  b64_negFrame_span_aux z

example : b60_F 0 ⊓ b64_Eminus = Submodule.span ℂ (Set.range (b64_negFrame 0)) :=
  b64_negFrame_span 0

/-- A three-frame spanning the negative graph plane at `z` has invertible head block and
graph coordinate `z`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1, §5 (graph charts of
the Grassmannian); `b60_frame_independent`. -/
theorem b64_graphCoord_of_span (z : Fin 9 → ℂ) (v : Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (hv : Submodule.span ℂ (Set.range v) = Submodule.span ℂ (Set.range (b64_negFrame z))) :
    IsUnit (b64_headBlock v) ∧ b64_graphCoord v = z :=
  b64_graphCoord_of_span_aux z v hv

example (z : Fin 9 → ℂ) :
    IsUnit (b64_headBlock (b64_negFrame z)) ∧ b64_graphCoord (b64_negFrame z) = z :=
  b64_graphCoord_of_span z _ rfl

/-- A three-frame of the negative eigenspace with invertible head block spans the
negative graph plane at its graph coordinate.
Source: Griffiths–Harris, Ch. 1, §5; `b60c_eigen_support`. -/
theorem b64_span_negFrame_graphCoord (v : Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (hv : ∀ j, v j ∈ b64_Eminus) (hu : IsUnit (b64_headBlock v)) :
    Submodule.span ℂ (Set.range v) =
      Submodule.span ℂ (Set.range (b64_negFrame (b64_graphCoord v))) :=
  b64_span_negFrame_graphCoord_aux v hv hu

example (v : Fin 3 → ℂ ⊗[ℤ] b60_Lattice) (hv : ∀ j, v j ∈ b64_Eminus)
    (hu : IsUnit (b64_headBlock v)) :
    Submodule.span ℂ (Set.range v) =
      Submodule.span ℂ (Set.range (b64_negFrame (b64_graphCoord v))) :=
  b64_span_negFrame_graphCoord v hv hu

/-- The coordinate of the chart filtration at `z` is `z`; in particular `b60_F` is
injective.
Source: van Geemen, LNM 1594, §5.10; G32 v0.16, §2.1. -/
theorem b64_coordOf_eq (z : Fin 9 → ℂ) : b64_coordOf (b60_F z) = z :=
  b64_coordOf_eq_aux z

example (z w : Fin 9 → ℂ) (h : b60_F z = b60_F w) : z = w := by
  rw [← b64_coordOf_eq z, h, b64_coordOf_eq w]

/-- Graph coordinates of frames with analytic eigen-coordinates and invertible head
blocks are analytic.
Source: Cramer's rule, Lang, *Algebra*, rev. 3rd ed., Ch. XIII, §4; analyticity of
`Ring.inverse` at units, Mathlib. -/
theorem b64_graphCoord_analyticOnNhd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (v : E → Fin 3 → ℂ ⊗[ℤ] b60_Lattice) (W : Set E)
    (hv : ∀ j p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr (v t j) p) W)
    (hu : ∀ t ∈ W, IsUnit (b64_headBlock (v t))) :
    AnalyticOnNhd ℂ (fun t => b64_graphCoord (v t)) W :=
  b64_graphCoord_analyticOnNhd_aux v W hv hu

example (v : ℂ → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (hv : ∀ j p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr (v t j) p) Set.univ)
    (hu : ∀ t ∈ (Set.univ : Set ℂ), IsUnit (b64_headBlock (v t))) :
    AnalyticOnNhd ℂ (fun t => b64_graphCoord (v t)) Set.univ :=
  b64_graphCoord_analyticOnNhd v Set.univ hv hu

/-- Instance check, computed directly: the negative graph frame has head block `1` at
every matrix point, and along the line `t ↦ (t, …, t)` its eigen-coordinates are entire.
So the hypotheses of `b64_graphCoord_analyticOnNhd` hold for a nonconstant family. -/
example (z : Fin 9 → ℂ) : b64_headBlock (b64_negFrame z) = 1 := by
  ext i j
  rw [b64_headBlock, Matrix.of_apply, b64_negFrame_repr, Matrix.one_apply]
  simp [Prod.ext_iff, Fin.ext_iff, eq_comm]
  refine (Finset.sum_eq_zero fun x _ => ?_).symm
  rw [ite_eq_right_iff]
  intro h
  omega

example (j : Fin 3) (p : Fin 2 × Fin 6) :
    AnalyticOnNhd ℂ (fun t : ℂ => b60c_eigenBasis.repr (b64_negFrame (fun _ => t) j) p)
      Set.univ := by
  intro t _
  simp only [b64_negFrame_repr, g32m_toMat, Matrix.of_apply]
  fun_prop

/-- Near each parameter, three members of a spanning family of chart filtrations have
negative parts framing the negative plane, with invertible head block.
Source: Lang, *Algebra*, Ch. XIII, §4 (a nonvanishing maximal minor persists nearby);
van Geemen, LNM 1594, §5.10. -/
theorem b64_local_subframe {E : Type*} [TopologicalSpace E] {ι : Type*} [Fintype ι]
    (u : E → ι → ℂ ⊗[ℤ] b60_Lattice) (F : E → Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (W : Set E) (hW : IsOpen W)
    (hu : ∀ k p, ContinuousOn (fun t => b60c_eigenBasis.repr (u t k) p) W)
    (hspan : ∀ t ∈ W, Submodule.span ℂ (Set.range (u t)) = F t)
    (hF : ∀ t ∈ W, ∃ z : Fin 9 → ℂ, F t = b60_F z) (t₀ : E) (ht₀ : t₀ ∈ W) :
    ∃ W' : Set E, IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧ ∃ σ : Fin 3 → ι, ∀ t ∈ W',
      IsUnit (b64_headBlock fun j => b64_negPart (u t (σ j))) ∧
      Submodule.span ℂ (Set.range fun j => b64_negPart (u t (σ j))) = F t ⊓ b64_Eminus :=
  b64_local_subframe_aux u F W hW hu hspan hF t₀ ht₀

/-- Instance check: the constant family of chart filtrations at `0`, spanned by the full
frame, satisfies every hypothesis of `b64_local_subframe`. -/
example : (∀ (k : Fin 2 × Fin 3) p, ContinuousOn
      (fun _ : ℂ => b60c_eigenBasis.repr (b60_frame 0 k) p) Set.univ) ∧
    (∀ t ∈ (Set.univ : Set ℂ),
      Submodule.span ℂ (Set.range (b60_frame 0)) = b60_F 0) ∧
    (∀ t ∈ (Set.univ : Set ℂ), ∃ z : Fin 9 → ℂ, b60_F 0 = b60_F z) :=
  ⟨fun _ _ => continuousOn_const, fun _ _ => rfl, fun _ _ => ⟨0, rfl⟩⟩

example {ι : Type} [Fintype ι] (u : ℂ → ι → ℂ ⊗[ℤ] b60_Lattice)
    (F : ℂ → Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (hu : ∀ k p, ContinuousOn (fun t => b60c_eigenBasis.repr (u t k) p) Set.univ)
    (hspan : ∀ t ∈ (Set.univ : Set ℂ), Submodule.span ℂ (Set.range (u t)) = F t)
    (hF : ∀ t ∈ (Set.univ : Set ℂ), ∃ z : Fin 9 → ℂ, F t = b60_F z) :
    ∃ W' : Set ℂ, IsOpen W' ∧ (0 : ℂ) ∈ W' ∧ W' ⊆ Set.univ ∧ ∃ σ : Fin 3 → ι, ∀ t ∈ W',
      IsUnit (b64_headBlock fun j => b64_negPart (u t (σ j))) ∧
      Submodule.span ℂ (Set.range fun j => b64_negPart (u t (σ j))) = F t ⊓ b64_Eminus :=
  b64_local_subframe u F Set.univ isOpen_univ hu hspan hF 0 trivial

/-- The implication from analytic spanning families of chart filtrations on an open set
to analyticity of their period coordinate on that set.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90
(1968), §1 (period maps in graph coordinates); Lang, *Algebra*, Ch. XIII, §4. -/
theorem b64_coordOf_analyticOnNhd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    (u : E → ι → ℂ ⊗[ℤ] b60_Lattice) (F : E → Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (W : Set E) (hW : IsOpen W)
    (hu : ∀ k p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr (u t k) p) W)
    (hspan : ∀ t ∈ W, Submodule.span ℂ (Set.range (u t)) = F t)
    (hF : ∀ t ∈ W, ∃ z : Fin 9 → ℂ, F t = b60_F z) :
    AnalyticOnNhd ℂ (fun t => b64_coordOf (F t)) W :=
  b64_coordOf_analyticOnNhd_aux u F W hW hu hspan hF

/-- Instance check: the constant family of chart filtrations at `0` satisfies every
hypothesis of `b64_coordOf_analyticOnNhd`. -/
example : (∀ (k : Fin 2 × Fin 3) p, AnalyticOnNhd ℂ
      (fun _ : Fin 10 → ℂ => b60c_eigenBasis.repr (b60_frame 0 k) p) Set.univ) ∧
    (∀ t ∈ (Set.univ : Set (Fin 10 → ℂ)),
      Submodule.span ℂ (Set.range (b60_frame 0)) = b60_F 0) ∧
    (∀ t ∈ (Set.univ : Set (Fin 10 → ℂ)), ∃ z : Fin 9 → ℂ, b60_F 0 = b60_F z) :=
  ⟨fun _ _ => analyticOnNhd_const, fun _ _ => rfl, fun _ _ => ⟨0, rfl⟩⟩

example : AnalyticOnNhd ℂ (fun _ : Fin 10 → ℂ => b64_coordOf (b60_F 0)) Set.univ :=
  b64_coordOf_analyticOnNhd (fun _ => b60_frame 0) (fun _ => b60_F 0) Set.univ isOpen_univ
    (fun _ _ => analyticOnNhd_const) (fun _ _ => rfl) (fun _ _ => ⟨0, rfl⟩)

/-- Instance check: the chart filtration at the origin of the domain satisfies the four
inputs of `b60c_fixed_filtration_chart`, using only statements with proofs on `main`. -/
example : Module.finrank ℂ (b60_F 0) = 6 ∧
    Module.finrank ℂ ↥(b60_F 0 ⊓ Module.End.eigenspace b60_omegaC
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
    Module.finrank ℂ ↥(b60_F 0 ⊓ Module.End.eigenspace b60_omegaC
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
    b2_IsRiemannForm b60_Lattice (b60_F 0) b60_E := by
  refine ⟨?_, (b60_weil_dimensions 0).2, (b60_weil_dimensions 0).1,
    (b60_riemann_iff 0).2 g32m_zero_mem⟩
  rw [b60_F, finrank_span_eq_card (b60_frame_independent 0)]
  rfl

/-- **Chain check toward `g32r_PeriodMap`.** For a family `F` of filtrations of the fixed
lattice over an open `V ⊆ ℂ¹⁰`, spanned by analytic families and satisfying the four
inputs of `b60c_fixed_filtration_chart` at each parameter, the function
`t ↦ b64_coordOf (F t)` fills the fields `period`, `analytic` and `mapsTo`. The other
fields enter as explicit binders, each stated with this `period`: `isog` is B6-4's later
comparison with the universal fibre, `curve`, `jet` and `jet_certified` are B6-5, and
`codiff` is B6-6. No field is derived here beyond `analytic` and `mapsTo`. -/
example (Fm : g32m_UniversalFamily) (P : g32h_PrymFamily) {ι : Type} [Fintype ι]
    (u : (Fin 10 → ℂ) → ι → ℂ ⊗[ℤ] b60_Lattice)
    (F : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (V : Set (Fin 10 → ℂ)) (hV : IsOpen V)
    (hu : ∀ k p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr (u t k) p) V)
    (hspan : ∀ t ∈ V, Submodule.span ℂ (Set.range (u t)) = F t)
    (hdim : ∀ t ∈ V, Module.finrank ℂ (F t) = 6)
    (hneg : ∀ t ∈ V, Module.finrank ℂ ↥(F t ⊓ Module.End.eigenspace b60_omegaC
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : ∀ t ∈ V, Module.finrank ℂ ↥(F t ⊓ Module.End.eigenspace b60_omegaC
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hR : ∀ t ∈ V, b2_IsRiemannForm b60_Lattice (F t) b60_E)
    (hisog : ∀ t (_ : t ∈ V) (hm : b64_coordOf (F t) ∈ g32m_Domain),
      ∃ s, g32t_KIsog (P.fiber s) (Fm.univ ⟨b64_coordOf (F t), hm⟩))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0) (curve_zero : curve 0 ∈ V)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ R : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit R ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (fun t => b64_coordOf (F t)) (curve θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * R) :
    Nonempty (g32r_PeriodMap Fm P) := by
  have hF : ∀ t ∈ V, ∃ τ : g32m_Domain, F t = b60_F τ := fun t ht =>
    b60c_fixed_filtration_chart (F t) (hdim t ht) (hneg t ht) (hpos t ht) (hR t ht)
  have hmaps : MapsTo (fun t => b64_coordOf (F t)) V (g32m_Domain : Set (Fin 9 → ℂ)) := by
    intro t ht
    obtain ⟨τ, h⟩ := hF t ht
    change b64_coordOf (F t) ∈ g32m_Domain
    rw [h, b64_coordOf_eq]
    exact τ.2
  exact ⟨{ V := V
           isOpen_V := hV
           period := fun t => b64_coordOf (F t)
           analytic := b64_coordOf_analyticOnNhd u F V hV hu hspan fun t ht =>
             let ⟨τ, h⟩ := hF t ht
             ⟨τ, h⟩
           mapsTo := hmaps
           isog := fun t ht => hisog t ht (hmaps ht)
           curve := curve
           curve_cont := curve_cont
           curve_zero := curve_zero
           jet := jet
           jet_certified := jet_certified
           codiff := codiff }⟩

end HodgeLean.Foundations.Program

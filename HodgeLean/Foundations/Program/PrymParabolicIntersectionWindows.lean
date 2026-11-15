import HodgeLean.Foundations.Program.PrymParabolicIntersectionWindowRays

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter Complex
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program

/-! ## The smooth step of B3's good segments -/

/-- The smooth step `τ ↦ smoothTransition (3 τ − 1)`, constant outside `[1/3, 2/3]`.
Source: `b3A_isGoodPath_segment`; Mathlib `Real.smoothTransition`. -/
def hga_step (τ : ℝ) : ℝ := Real.smoothTransition (3 * τ - 1)

theorem hga_step_mem (τ : ℝ) : hga_step τ ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem hga_step_contDiff : ContDiff ℝ 1 hga_step :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem hga_smoothTransition_half : Real.smoothTransition (1 / 2) = 1 / 2 := by
  unfold Real.smoothTransition
  have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h]
  have hp : 0 < expNegInvGlue (1 / 2) := expNegInvGlue.pos_of_pos (by norm_num)
  field_simp
  ring

theorem hga_step_half : hga_step (1 / 2) = 1 / 2 := by
  unfold hga_step
  rw [show (3 : ℝ) * (1 / 2) - 1 = 1 / 2 by norm_num, hga_smoothTransition_half]

theorem hga_smoothTransition_strictMonoOn :
    StrictMonoOn Real.smoothTransition (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) Real.smoothTransition.continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  obtain ⟨d, hd, hD⟩ := b3Rest_smoothTransition_hasDerivAt_pos hx
  rw [hD.deriv]
  exact hd

theorem hga_step_eq_half_iff (τ : ℝ) : hga_step τ = 1 / 2 ↔ τ = 1 / 2 := by
  constructor
  · intro h
    unfold hga_step at h
    by_cases h0 : 3 * τ - 1 ≤ 0
    · rw [Real.smoothTransition.zero_of_nonpos h0] at h; norm_num at h
    by_cases h1 : 1 ≤ 3 * τ - 1
    · rw [Real.smoothTransition.one_of_one_le h1] at h; norm_num at h
    push Not at h0 h1
    have hmem : 3 * τ - 1 ∈ Icc (0 : ℝ) 1 := ⟨h0.le, h1.le⟩
    have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have := hga_smoothTransition_strictMonoOn.injOn hmem hhalf
      (h.trans hga_smoothTransition_half.symm)
    linarith
  · rintro rfl
    exact hga_step_half

theorem hga_step_eventually_zero : ∀ᶠ τ in 𝓝 (0 : ℝ), hga_step τ = 0 := by
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with τ hτ
  exact Real.smoothTransition.zero_of_nonpos (by have : τ < 1 / 3 := hτ; linarith)

theorem hga_step_eventually_one : ∀ᶠ τ in 𝓝 (1 : ℝ), hga_step τ = 1 := by
  filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with τ hτ
  exact Real.smoothTransition.one_of_one_le (by have : 2 / 3 < τ := hτ; linarith)

theorem hga_step_deriv_half : 0 < deriv hga_step (1 / 2) := by
  obtain ⟨d, hd, hD⟩ := b3Rest_smoothTransition_hasDerivAt_pos
    (show (3 : ℝ) * (1 / 2) - 1 ∈ Ioo (0 : ℝ) 1 by norm_num)
  have h2 : HasDerivAt (fun τ : ℝ ↦ 3 * τ - 1) 3 (1 / 2) := by
    simpa using ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 3).sub_const 1
  have := hD.comp (1 / 2 : ℝ) h2
  change 0 < deriv (Real.smoothTransition ∘ fun τ : ℝ ↦ 3 * τ - 1) (1 / 2)
  rw [this.deriv]
  positivity

/-! ## Face points -/

/-- The point at parameter `θ` (projected to `[0, 1]`) of the face `k` of the standard simplex.
Source: `hg5_face`. -/
def hga_facePt (k : Fin 3) (θ : ℝ) : Convexity.StdSimplex ℝ (Fin 3) :=
  Convexity.StdSimplex.map k.succAbove
    (Convexity.StdSimplex.homeomorphI.symm (Set.projIcc 0 1 zero_le_one θ))

theorem hga_face_facePt {T : Type} [TopologicalSpace T] (σ : C(Convexity.StdSimplex ℝ (Fin 3), T))
    (k : Fin 3) (θ : ℝ) :
    σ (hga_facePt k θ) = hg5_face σ k (Set.projIcc 0 1 zero_le_one θ) := rfl

/-! ## Window data on a base edge -/

/-- **Window data on a base edge**: a crossing parameter `s` on the face `ke` of the base triangle
`τe` (where the edge is the straight line `P + φ(θ) v`), and two rays `Mo`, `Mi` from the points at
parameter `s` of the faces `ko`, `ki` of the two base triangles `τo`, `τi` along the edge, whose
plane images are the two halves `P ± λ η i v` of a segment crossing the edge.
Source: barycentric dual cells (Hatcher, §3.3); the explicit rays of
`PrymParabolicIntersectionWindowRays.lean`. -/
structure hga_WindowSpec where
  τo : hg2_Tri Unit 13
  τi : hg2_Tri Unit 13
  τe : hg2_Tri Unit 13
  ko : Fin 3
  ki : Fin 3
  ke : Fin 3
  s : ℝ
  δ : ℝ
  η : ℝ
  P : ℂ
  v : ℂ
  φ : ℝ → ℝ
  Mo : C(unitInterval, Convexity.StdSimplex ℝ (Fin 3))
  Mi : C(unitInterval, Convexity.StdSimplex ℝ (Fin 3))
  hδ : 0 < δ
  hs0 : δ < s
  hs1 : s + δ < 1
  hη : 0 < η
  hv : v ≠ 0
  Mo0 : Mo 0 = hga_facePt ko s
  Mi0 : Mi 0 = hga_facePt ki s
  Mo_pos : ∀ x : unitInterval, 0 < (x : ℝ) → ∀ j, 0 < (Mo x).weights j
  Mi_pos : ∀ x : unitInterval, 0 < (x : ℝ) → ∀ j, 0 < (Mi x).weights j
  Mo_img : ∀ x : unitInterval,
    hg5_tri τo (Mo x) = (((P + (((x : ℝ) * η : ℝ) : ℂ) * (I * v)) : ℂ) : OnePoint ℂ)
  Mi_img : ∀ x : unitInterval,
    hg5_tri τi (Mi x) = (((P - (((x : ℝ) * η : ℝ) : ℂ) * (I * v)) : ℂ) : OnePoint ℂ)
  E_img : ∀ θ ∈ Icc (s - δ) (s + δ),
    hg5_tri τe (hga_facePt ke θ) = (((P + ((φ θ : ℝ) : ℂ) * v) : ℂ) : OnePoint ℂ)
  φ_s : φ s = 0
  φ_inj : InjOn φ (Icc (s - δ) (s + δ))
  φ_diff : ContDiffOn ℝ 1 φ (Ioo (s - 2 * δ) (s + 2 * δ))
  φ_deriv : 0 < deriv φ s
  im_dual : ∀ x ∈ Icc (-1 : ℝ) 1, 1 ≤ |(P + ((x * η : ℝ) : ℂ) * (I * v)).im|
  im_prim : ∀ θ ∈ Icc (s - δ) (s + δ), 1 ≤ |(P + ((φ θ : ℝ) : ℂ) * v).im|

namespace hga_WindowSpec

variable (W : hga_WindowSpec)

/-- The plane curve of the dual window, `τ ↦ P + η (1 − 2 σ(τ)) i v`.
Source: the straight segment through the crossing point. -/
def dualCurve (τ : ℝ) : ℂ := W.P + (((1 - 2 * hga_step τ) * W.η : ℝ) : ℂ) * (I * W.v)

/-- The edge parameter of the primal window, `τ ↦ s + δ (2 σ(τ) − 1)`.
Source: the straight part of the edge about the crossing point. -/
def primParam (τ : ℝ) : ℝ := W.s + W.δ * (2 * hga_step τ - 1)

/-- The plane curve of the primal window.
Source: `hga_WindowSpec.E_img`. -/
def primCurve (τ : ℝ) : ℂ := W.P + ((W.φ (W.primParam τ) : ℝ) : ℂ) * W.v

theorem primParam_mem (τ : ℝ) : W.primParam τ ∈ Icc (W.s - W.δ) (W.s + W.δ) := by
  obtain ⟨h0, h1⟩ := hga_step_mem τ
  unfold primParam
  have := W.hδ
  constructor <;> nlinarith

theorem dualCurve_contDiff : ContDiff ℝ 1 W.dualCurve := by
  unfold dualCurve
  have h : ContDiff ℝ 1 (fun τ ↦ (1 - 2 * hga_step τ) * W.η) :=
    (contDiff_const.sub (contDiff_const.mul hga_step_contDiff)).mul contDiff_const
  exact contDiff_const.add ((ofRealCLM.contDiff.comp h).mul contDiff_const)

theorem primCurve_contDiff : ContDiff ℝ 1 W.primCurve := by
  unfold primCurve
  have hθ : ContDiff ℝ 1 W.primParam := by
    unfold primParam
    exact contDiff_const.add (contDiff_const.mul
      ((contDiff_const.mul hga_step_contDiff).sub contDiff_const))
  have hφ : ContDiff ℝ 1 (W.φ ∘ W.primParam) :=
    W.φ_diff.comp_contDiff hθ (fun τ ↦ by
      obtain ⟨h0, h1⟩ := W.primParam_mem τ
      have := W.hδ
      constructor <;> linarith)
  exact contDiff_const.add ((ofRealCLM.contDiff.comp hφ).mul contDiff_const)

theorem dualCurve_im (τ : ℝ) : 1 ≤ |(W.dualCurve τ).im| := by
  obtain ⟨h0, h1⟩ := hga_step_mem τ
  exact W.im_dual _ ⟨by linarith, by linarith⟩

theorem primCurve_im (τ : ℝ) : 1 ≤ |(W.primCurve τ).im| :=
  W.im_prim _ (W.primParam_mem τ)

end hga_WindowSpec

/-! ## Path chains inside a realized triangle -/

section TriangleChains

variable {T : Type} [TopologicalSpace T]

instance hga_simplex_pathConnected : PathConnectedSpace (Convexity.StdSimplex ℝ (Fin 3)) := by
  haveI := hga_triangle_contractible
  infer_instance

/-- The path chain of a realized triangle `σ` between two points of the simplex, along any path in
the simplex (all such paths give the same chain).
Source: `hga_pathChain_contractible`, `hga_triangle_contractible`. -/
def hga_TL (σ : C(Convexity.StdSimplex ℝ (Fin 3), T)) (a b : Convexity.StdSimplex ℝ (Fin 3)) :
    b6m_chainQuotient (CategoryTheory.Functor.obj TopCat.toSSet (TopCat.of T)) :=
  b6m_pathChain (σ.comp (PathConnectedSpace.somePath a b).toContinuousMap)

theorem hga_TL_eq (σ : C(Convexity.StdSimplex ℝ (Fin 3), T))
    (g : C(unitInterval, Convexity.StdSimplex ℝ (Fin 3))) :
    b6m_pathChain (σ.comp g) = hga_TL σ (g 0) (g 1) := by
  haveI := hga_triangle_contractible
  exact hga_pathChain_contractible σ g _ (by simp) (by simp)

theorem hga_TL_trans (σ : C(Convexity.StdSimplex ℝ (Fin 3), T))
    (a b c : Convexity.StdSimplex ℝ (Fin 3)) :
    hga_TL σ a b + hga_TL σ b c = hga_TL σ a c := by
  let p := PathConnectedSpace.somePath a b
  let q := PathConnectedSpace.somePath b c
  have h : b6m_pathChain (σ.comp (p.trans q).toContinuousMap) = hga_TL σ a c := by
    rw [hga_TL_eq]
    congr 1
    · exact (p.trans q).source
    · exact (p.trans q).target
  rw [← h]
  have e : σ.comp (p.trans q).toContinuousMap = ((p.trans q).map σ.continuous).toContinuousMap := rfl
  rw [e, Path.map_trans, b6m_pathChain_trans]
  rfl

theorem hga_TL_self (σ : C(Convexity.StdSimplex ℝ (Fin 3), T)) (a : Convexity.StdSimplex ℝ (Fin 3)) :
    hga_TL σ a a = 0 := by
  have h := hga_TL_trans σ a a a
  have := congrArg (· - hga_TL σ a a) h
  simpa using this

theorem hga_TL_symm (σ : C(Convexity.StdSimplex ℝ (Fin 3), T)) (a b : Convexity.StdSimplex ℝ (Fin 3)) :
    hga_TL σ b a = -hga_TL σ a b := by
  have h := hga_TL_trans σ a b a
  rw [hga_TL_self] at h
  exact eq_neg_of_add_eq_zero_right h

end TriangleChains

end HodgeLean.Foundations.Program

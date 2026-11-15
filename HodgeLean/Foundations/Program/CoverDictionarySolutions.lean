import HodgeLean.Foundations.Program.CoverDictionaryContinuation
import HodgeLean.Foundations.Program.CoverDictionaryRegular

/-! # B6-5 stage 5d, stage five: pulled-back fundamental solutions on the fibres

The regular locus of a fibre is the complement of finitely many points, hence path-connected
and locally path-connected. Over the quotient covering of stage three, the continuation of
`caf_continuation` is a solution of the system in the `s`-coordinate (the disc solution composed
with the holomorphic `s`-function), and the deck law `Y (h • y) = Y y ρ(h⁻¹)` is the law with
`ρ̄(h)ᵀ = ρ(h⁻¹)` (the matrices are unitary). Assembling the fibre solutions over the path gives
the record `b65g_Solutions`, with `conj = true`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

section Fibre

variable {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
  (t : b6t_polydisc c)

/-- The fibres of the projection of a fibre are finite (they are orbits of the deck group). -/
theorem b65g_projection_fibre_finite (y : OnePoint ℂ) :
    (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t ⁻¹' {y}).Finite := by
  by_cases h : (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t ⁻¹'
    {y}).Nonempty
  · obtain ⟨x₀, hx₀⟩ := h
    refine (Set.finite_range (fun h : b4b_Group ↦ h • x₀)).subset fun x hx ↦ ?_
    exact (D.hgal t).2 x₀ x ((mem_singleton_iff.mp hx₀).trans (mem_singleton_iff.mp hx).symm)
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact finite_empty

/-- **The regular locus has finite complement.** -/
theorem b65g_good_compl_finite {a b : ℂ} (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (poles : Fin 4 ⊕ Fin 12 → ℂ) : (b65g_good D t a b poles)ᶜ.Finite := by
  set π := b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t
  set B : Set (OnePoint ℂ) := {OnePoint.infty} ∪ (((↑) : ℂ → OnePoint ℂ) ''
    ({z | b - z * (b - a) = 0} ∪
      (fun z : ℂ ↦ b65g_sCoord a b (z : OnePoint ℂ)) ⁻¹' Set.range poles))
  have h1 : {z : ℂ | b - z * (b - a) = 0}.Finite := by
    refine (Set.finite_singleton (b / (b - a))).subset fun z hz ↦ ?_
    simp only [mem_ofPred_eq] at hz
    simp only [mem_singleton_iff]
    field_simp
    linear_combination -hz
  have h2 : ((fun z : ℂ ↦ b65g_sCoord a b (z : OnePoint ℂ)) ⁻¹' Set.range poles).Finite :=
    (Set.finite_range poles).preimage (b65g_sCoord_injective hab hba).injOn
  have hB : B.Finite := (finite_singleton _).union ((h1.union h2).image _)
  refine (hB.preimage' (fun y _ ↦ b65g_projection_fibre_finite D t y)).subset ?_
  intro x hx
  simp only [mem_compl_iff] at hx
  simp only [mem_preimage, B, mem_union, mem_singleton_iff, mem_image, mem_ofPred_eq]
  cases hpx : π x with
  | infty => exact Or.inl hpx
  | coe z =>
    refine Or.inr ⟨z, ?_, hpx.symm⟩
    by_contra hcon
    push Not at hcon
    exact hx ⟨z, hpx, hcon.1, hcon.2⟩

theorem b65g_good_isOpen {a b : ℂ} (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (poles : Fin 4 ⊕ Fin 12 → ℂ) : IsOpen (b65g_good D t a b poles) := by
  have := (b65g_good_compl_finite D t hab hba poles).isClosed
  rwa [isClosed_compl_iff] at this

theorem b65g_good_pathConnectedSpace {a b : ℂ} (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (poles : Fin 4 ⊕ Fin 12 → ℂ) : PathConnectedSpace (b65g_goodSub D t a b poles) := by
  have h := caf_isPathConnected_compl_finite (b65z_fibre c D.C t) _
    (b65g_good_compl_finite D t hab hba poles)
  rw [compl_compl] at h
  exact isPathConnected_iff_pathConnectedSpace.mp h

theorem b65g_good_locPathConnectedSpace {a b : ℂ} (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (poles : Fin 4 ⊕ Fin 12 → ℂ) :
    LocallyPathConnectedSpace (b65g_goodSub D t a b poles) := by
  have : LocallyPathConnectedSpace (b65z_fibre c D.C t) :=
    ChartedSpace.locallyPathConnectedSpace ℂ _
  exact (b65g_good_isOpen D t hab hba poles).locallyPathConnectedSpace

/-- The `s`-function is holomorphic at every point over a finite `z` with finite `s`. -/
theorem b65g_sFun_hasMFDerivAt {a b : ℂ} (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (y : b65z_fibre c D.C t) (z : ℂ)
    (hy : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t y = z)
    (hz : b - z * (b - a) ≠ 0) :
    HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sFun D t a b) y
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sFun D t a b) y) := by
  obtain ⟨L, hL, -⟩ := b65g_sCoord_hasMFDerivAt hab hba hz _ hy
  have hP := ((D.hk t y).mdifferentiableAt (by simp)).hasMFDerivAt
  exact (hL.comp y hP).mdifferentiableAt.hasMFDerivAt

end Fibre

/-- **`ρ̄(h)ᵀ = ρ(h⁻¹)`**: the natural matrices are unitary, so the transpose of the conjugate
matrix is the matrix of the inverse (`b63l_toMatrix_inv_eq_star`). This is the convention of
`b65s_column`, which uses `ρ(h⁻¹)`. -/
theorem b65g_mat_true_transpose (h : b4b_Group) :
    LinearMap.toContinuousLinearMap (Matrix.toLin' (b65g_mat true h)ᵀ) =
      b65r_operator (b4b_toMatrix h⁻¹) := by
  have hm : (b65g_mat true h)ᵀ = b4b_toMatrix h⁻¹ := by
    rw [b63l_toMatrix_inv_eq_star]
    ext i j
    simp [b65g_mat, Matrix.star_apply]
  rw [hm]
  rfl

section Continuation

variable (p : Fin 12 → ℂ) (O : b65p_Outputs p) {g : Fin 13 → b4b_Group}
  (D : b65z_SharedFamily (b65z_centre p) g)

/-- **Continuation on one fibre, with `ρ̄`.** On the fibre over `b65p_curve p θ`, for a
quotient-covering proof of the `s`-projection with the all-loop transfer property, there is a
function on the fibre which at every regular point is invertible, solves the system at `θ` in the
`s`-coordinate and satisfies `Y (h • y) = Y y ρ̄(h)ᵀ`. -/
theorem b65g_fibre_continuation_bar (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) O.radius)
    (t : b6t_polydisc (b65z_centre p)) (_ht : t.val = b65p_curve p θ)
    (hπ : IsQuotientCoveringMap (b65g_sProj D t (b65p_moving p θ 10) (b65p_moving p θ 11)
      (b65p_poles p θ)) b4b_Group)
    (hL : b65g_loopTransfer D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)
      (O.residue θ) hπ) :
    ∃ Y : b65z_fibre (b65z_centre p) D.C t → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ),
      ∀ y ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ),
        IsUnit (Y y) ∧
        (MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) Y y ∧
          ∀ w : TangentSpace 𝓘(ℂ, ℂ) y,
            (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) Y y w :
              (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) =
            b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨y, w⟩ •
              (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ)
                (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) y) * Y y)) ∧
        ∀ h : b4b_Group, Y (h • y) = Y y * LinearMap.toContinuousLinearMap
          (Matrix.toLin' (b65g_mat true h)ᵀ) := by
  classical
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθ
  set a := b65p_moving p θ 10
  set b := b65p_moving p θ 11
  set poles := b65p_poles p θ
  have hab' : a * b ≠ 0 := mul_ne_zero ha hb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have := b65g_good_pathConnectedSpace D t hab' hba poles
  have := b65g_good_locPathConnectedSpace D t hab' hba poles
  obtain ⟨x, u, C, hT⟩ := hL
  have hUo : IsOpen (b65g_U poles) := (Set.finite_range poles).isClosed.isOpen_compl
  set A := b65p_coefficient (Fin 4 → ℂ) poles (O.residue θ)
  have hA : AnalyticOnNhd ℂ A (b65g_U poles) := b65g_coefficient_analytic _ _
  obtain ⟨Yv, hunit, hdeck, hloc⟩ := caf_continuation hUo A hA hπ x u C hT
  let Y : b65z_fibre (b65z_centre p) D.C t → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) := fun y ↦
    if hy : y ∈ b65g_good D t a b poles then Yv ⟨y, hy⟩ else 1
  have hYv : ∀ y (hy : y ∈ b65g_good D t a b poles), Y y = Yv ⟨y, hy⟩ := fun y hy ↦ dite_eq_left hy
  have hgo := b65g_good_isOpen D t hab' hba poles
  refine ⟨Y, fun y hy ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [hYv y hy]
    exact hunit _
  · let v : b65g_goodSub D t a b poles := ⟨y, hy⟩
    set s₀ := b65g_sFun D t a b y
    have hs₀ : (b65g_sProj D t a b poles v).val = s₀ := rfl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUo s₀ (b65g_sProj D t a b poles v).property
    have hl := hloc v r hr (by rw [hs₀]; exact hball)
    have hev : Y =ᶠ[𝓝 y] fun w ↦ b65f_segment (Fin 4 → ℂ) A s₀ (b65g_sFun D t a b w) * Y y := by
      rw [← hgo.isOpenEmbedding_subtypeVal.map_nhds_eq v, Filter.EventuallyEq,
        Filter.eventually_map]
      filter_upwards [hl] with w hw
      rw [hYv _ w.property, hYv y hy]
      exact hw
    obtain ⟨-, hseg1, -, hder, -⟩ := b65f_segment_solution (Fin 4 → ℂ) A s₀ r hr (hA.mono hball)
    have hg : HasDerivAt (fun z ↦ b65f_segment (Fin 4 → ℂ) A s₀ z * Y y)
        (A s₀ * b65f_segment (Fin 4 → ℂ) A s₀ s₀ * Y y) s₀ :=
      (hder s₀ (mem_ball_self hr)).mul_const _
    obtain ⟨z, hz, hw, -⟩ := hy
    have hs := b65g_sFun_hasMFDerivAt D t hab' hba y z hz hw
    have hg' : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
        (fun z ↦ b65f_segment (Fin 4 → ℂ) A s₀ z * Y y) (b65g_sFun D t a b y)
        ((1 : ℂ →L[ℂ] ℂ).smulRight (A s₀ * b65f_segment (Fin 4 → ℂ) A s₀ s₀ * Y y)) :=
      hasMFDerivAt_iff_hasFDerivAt.mpr hg.hasFDerivAt
    have hY := (hg'.comp y hs).congr_of_eventuallyEq hev
    refine ⟨hY.mdifferentiableAt, fun w ↦ ?_⟩
    rw [hY.mfderiv]
    simp only [ContinuousLinearMap.comp_apply, hseg1, mul_one]
    rfl
  · intro h
    rw [hYv _ ((b65g_goodSub D t a b poles).smul_mem h hy), hYv y hy, b65g_mat_true_transpose]
    exact hdeck h ⟨y, hy⟩

/-- **Continuation on one fibre** (planned signature of stage five): a function on the fibre and
a choice of `ρ` or `ρ̄` with invertibility, the system in the `s`-coordinate and the deck law at
every regular point. The choice is `ρ̄` (`b65g_fibre_continuation_bar`). -/
theorem b65g_fibre_continuation (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) O.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (hπ : IsQuotientCoveringMap (b65g_sProj D t (b65p_moving p θ 10) (b65p_moving p θ 11)
      (b65p_poles p θ)) b4b_Group)
    (hL : b65g_loopTransfer D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)
      (O.residue θ) hπ) :
    ∃ Y : b65z_fibre (b65z_centre p) D.C t → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ), ∃ conj : Bool,
      ∀ y ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ),
        IsUnit (Y y) ∧
        (MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) Y y ∧
          ∀ w : TangentSpace 𝓘(ℂ, ℂ) y,
            (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) Y y w :
              (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) =
            b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨y, w⟩ •
              (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ)
                (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) y) * Y y)) ∧
        ∀ h : b4b_Group, Y (h • y) = Y y * LinearMap.toContinuousLinearMap
          (Matrix.toLin' (b65g_mat conj h)ᵀ) := by
  obtain ⟨Y, hY⟩ := b65g_fibre_continuation_bar p O D θ hθ t ht hπ hL
  exact ⟨Y, true, hY⟩

/-- **Assembling the fibre solutions** over the path into the record `b65g_Solutions`: from a
radius inside the record's radius and, on the fibre over each `b65p_curve p θ` in that disc, a
function with invertibility, the system and the deck law for a fixed `conj` at the regular
points. -/
theorem b65g_assemble (ε : ℝ) (hε : 0 < ε) (hεO : ε ≤ O.radius) (conj : Bool)
    (h : ∀ θ ∈ ball (0 : ℂ) ε, ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∃ Y : b65z_fibre (b65z_centre p) D.C t → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ),
      ∀ y ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ),
        IsUnit (Y y) ∧
        (MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) Y y ∧
          ∀ w : TangentSpace 𝓘(ℂ, ℂ) y,
            (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) Y y w :
              (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) =
            b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨y, w⟩ •
              (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ)
                (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) y) * Y y)) ∧
        ∀ h : b4b_Group, Y (h • y) = Y y * LinearMap.toContinuousLinearMap
          (Matrix.toLin' (b65g_mat conj h)ᵀ)) :
    Nonempty (b65g_Solutions p O D) := by
  classical
  choose Yf hYf using h
  let Y : ℂ → b6t_polydisc (b65z_centre p) × D.C → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) :=
    fun θ q ↦ if hq : θ ∈ ball (0 : ℂ) ε ∧ q.1.val = b65p_curve p θ then
      Yf θ hq.1 q.1 hq.2 ⟨q, rfl⟩ else 0
  have key : ∀ θ (hθ : θ ∈ ball (0 : ℂ) ε) (t : b6t_polydisc (b65z_centre p))
      (ht : t.val = b65p_curve p θ),
      (fun y : b65z_fibre (b65z_centre p) D.C t ↦ Y θ y.val) = Yf θ hθ t ht := by
    intro θ hθ t ht
    funext y
    obtain ⟨⟨q₁, q₂⟩, hq⟩ := y
    change q₁ = t at hq
    subst hq
    exact dite_eq_left (⟨hθ, ht⟩ : θ ∈ ball (0 : ℂ) ε ∧ q₁.val = b65p_curve p θ)
  have key' : ∀ θ (hθ : θ ∈ ball (0 : ℂ) ε) (t : b6t_polydisc (b65z_centre p))
      (ht : t.val = b65p_curve p θ) (y : b65z_fibre (b65z_centre p) D.C t),
      Y θ y.val = Yf θ hθ t ht y := fun θ hθ t ht y ↦ congrFun (key θ hθ t ht) y
  refine ⟨⟨ε, hε, hεO, conj, Y, ?_, ?_, ?_⟩⟩
  · intro θ hθ t ht y hy
    rw [key' θ hθ t ht]
    exact (hYf θ hθ t ht y hy).1
  · intro θ hθ t ht y hy
    rw [key θ hθ t ht, key' θ hθ t ht]
    exact (hYf θ hθ t ht y hy).2.1
  · intro θ hθ t ht y hy k
    rw [key' θ hθ t ht, key' θ hθ t ht]
    exact (hYf θ hθ t ht y hy).2.2 k

/-- **The cover solutions** from the identification `hT` of the base system with the column
monodromy of the atlas cover: all-loop transfer to nearby parameters (stage three), continuation
on each fibre and assembly, with `conj = true`. -/
theorem b65g_cover_solutions_main (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ :
            C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val) :
    Nonempty (b65g_Solutions p O D) := by
  obtain ⟨ε, hε, hεO, hall⟩ := b65g_all_loop_transfer p O g D e he x u₀ C hT
  refine b65g_assemble p O D ε hε hεO true fun θ hθ t ht ↦ ?_
  obtain ⟨hπ, hL⟩ := hall θ hθ t ht
  exact b65g_fibre_continuation_bar p O D θ (ball_subset_ball hεO hθ) t ht hπ hL

end Continuation

end HodgeLean.Foundations.Program

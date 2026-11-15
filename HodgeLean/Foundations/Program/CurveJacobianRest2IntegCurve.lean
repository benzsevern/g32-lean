import HodgeLean.Foundations.Program.CurveJacobianRest2Integ
import HodgeLean.Foundations.Program.CurveJacobianRestAJ

/-! # Track B3, lane Rest2: the integration cocycle of a holomorphic form on a curve

For a compact connected Riemann surface with a continuous Abel–Jacobi map `aj` (discrete period
lattice), the covering `ℂ^g → J(C)` in linear coordinates is additive, and the lifted cocycle of
`aj` with the period functional at `θ` is the **integration cocycle** `b3Rest2_integCocycle θ`.
Its value on the simplex of a loop `p` with a `C¹` representative `γ` is the period of `γ` at `θ`
(`b3Rest2_integCocycle_loop`): `t ↦ aj(γ 0) + [w(t)]`, where `w(t)` has the periods
`∫₀ᵗ θⱼ(γ, γ')` on a basis, is a continuous lift of `aj ∘ γ` (the Abel–Jacobi property for the
paths `s ↦ γ(t s)`).
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold Metric CategoryTheory
open scoped Topology ContDiff Simplicial TensorProduct

namespace HodgeLean.Foundations.Program

open HodgeLean.Adapters

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-! ## Reparametrized path periods -/

attribute [local instance] b3Forms_isManifold_real in
theorem b3Rest2_velocity_scale [FiniteDimensional ℂ E] {γ : ℝ → C}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (c s : ℝ) :
    b3_velocity E C (fun s ↦ γ (c * s)) s = c • b3_velocity E C γ (c * s) := by
  have hγc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun s ↦ γ (c * s)) :=
    hγ.comp (contDiff_const.mul contDiff_id).contMDiff
  rw [b3Forms_velocity_eq_b3, b3Forms_velocity_eq_b3,
    b3Forms_velocity_eq (hγc.mdifferentiableAt one_ne_zero),
    b3Forms_velocity_eq (hγ.mdifferentiableAt one_ne_zero)]
  exact deriv_comp_mul_left (f := chartAt E (γ (c * s)) ∘ γ) c s

theorem b3Rest2_hol_smul_real [FiniteDimensional ℂ E] (θ : b3_HolForm E C) (x : C) (c : ℝ)
    (v : TangentSpace 𝓘(ℂ, E) x) :
    θ.1 ⟨x, c • v⟩ = (c : ℂ) * θ.1 ⟨x, v⟩ := by
  have h := θ.2.2 x (c : ℂ) v 0
  have h0 : θ.1 ⟨x, 0⟩ = 0 := b3Forms_hol_zero θ x
  rw [add_zero, h0, add_zero, Complex.coe_smul] at h
  exact h

/-- **Periods of `s ↦ γ(c s)`** are integrals over `[0, c]`. -/
theorem b3Rest2_pathPeriod_scale [FiniteDimensional ℂ E] {γ : ℝ → C}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (c : ℝ) (θ : b3_HolForm E C) :
    b3_pathPeriod E C (fun s ↦ γ (c * s)) θ =
      ∫ s in (0 : ℝ)..c, θ.1 ⟨γ s, b3_velocity E C γ s⟩ := by
  simp only [b3_pathPeriod, b3_pathIntegral, b3Rest2_velocity_scale hγ, b3Rest2_hol_smul_real]
  have := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (fun s ↦ θ.1 ⟨γ s, b3_velocity E C γ s⟩) c
  simp only [mul_zero, mul_one] at this
  rw [← this, Complex.real_smul, ← intervalIntegral.integral_const_mul]

/-! ## The covering in linear coordinates and the integration cocycle -/

section Cocycle

variable [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

/-- The class `(ℂ ⊗ Λ) ⧸ F`. -/
abbrev b3Rest2_QJ (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace C]
    [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C] : Type :=
  (ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C

/-- Linear coordinates of `(ℂ ⊗ Λ) ⧸ F`. -/
abbrev b3Rest2_VJ (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace C]
    [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C] : Type :=
  Fin (Module.finrank ℂ (b3Rest2_QJ E C)) → ℂ

set_option maxHeartbeats 400000 in
/-- **The covering of the Jacobian in linear coordinates, as an additive map.** -/
def b3Rest2_covHom : b3Rest2_VJ E C →+ b3_Jacobian E C where
  toFun := b2_torusCover (b3_periodLattice E C) (b3_periodF E C)
  map_zero' := by
    show QuotientAddGroup.mk ((b2_coord (b3Rest2_QJ E C)).symm 0) = _
    rw [map_zero]
    rfl
  map_add' v w := by
    show QuotientAddGroup.mk ((b2_coord (b3Rest2_QJ E C)).symm (v + w)) =
      QuotientAddGroup.mk ((b2_coord (b3Rest2_QJ E C)).symm v) +
        QuotientAddGroup.mk ((b2_coord (b3Rest2_QJ E C)).symm w)
    rw [map_add]
    rfl

theorem b3Rest2_covHom_coord (w : b3Rest2_QJ E C) :
    b3Rest2_covHom (b2_coord (b3Rest2_QJ E C) w) = QuotientAddGroup.mk w :=
  b3Rest_torusCover_coord w

theorem b3Rest2_covHom_spec :
    IsCoveringMap (b3Rest2_covHom (E := E) (C := C)) ∧
      Function.Surjective (b3Rest2_covHom (E := E) (C := C)) := by
  refine ⟨b2_torusCover_isCoveringMap (b3_periodF E C), fun x ↦ ?_⟩
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact ⟨b2_coord (b3Rest2_QJ E C) w, b3Rest2_covHom_coord w⟩

/-- The period functional at `θ` in linear coordinates. -/
def b3Rest2_ellV (θ : b3_HolForm E C) : b3Rest2_VJ E C →+ ℂ where
  toFun v := (b3_periodF E C).liftQ (b3_cplxPeriod E C) le_rfl
    ((b2_coord (b3Rest2_QJ E C)).symm v) θ
  map_zero' := by simp
  map_add' v w := by simp

theorem b3Rest2_ellV_coord (θ : b3_HolForm E C) (w : b3Rest2_QJ E C) :
    b3Rest2_ellV θ (b2_coord (b3Rest2_QJ E C) w) =
      (b3_periodF E C).liftQ (b3_cplxPeriod E C) le_rfl w θ := by
  simp [b3Rest2_ellV]

variable (aj : C → b3_Jacobian E C) (haj : Continuous aj)

/-- **The integration cocycle of a holomorphic form**, composed with an additive map
`g : ℂ → ℂ` (the identity, or the real part). -/
def b3Rest2_integCocycle (g : ℂ →+ ℂ) (θ : b3_HolForm E C) :
    AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of C)) 1 :=
  b3Rest2_liftCocycle b3Rest2_covHom b3Rest2_covHom_spec aj haj (g.comp (b3Rest2_ellV θ))

example (v₀ w : b3Rest2_VJ E C) :
    b3Rest2_covHom (v₀ + w) = b3Rest2_covHom v₀ + b3Rest2_covHom w := map_add _ _ _

example (v₀ w : b3Rest2_VJ E C) (a b : b3_Jacobian E C) (h1 : b3Rest2_covHom v₀ = a)
    (h2 : b3Rest2_covHom w = b) :
    b3Rest2_covHom v₀ + b3Rest2_covHom w = a + b := congrArg₂ (· + ·) h1 h2

theorem b3Rest2_covHom_jacMk (w : b3Rest2_QJ E C) (u : ℂ ⊗[ℤ] b3_periodLattice E C)
    (hw : w = Submodule.Quotient.mk u) :
    b3Rest2_covHom (b2_coord (b3Rest2_QJ E C) w) = b3A_jacMk u := by
  rw [b3Rest2_covHom_coord, hw]
  rfl

/-- The periods `∫₀ᵗ θⱼ(γ, γ')` of a path on a family of forms. -/
def b3Rest2_Γ {ι : Type} (θs : ι → b3_HolForm E C) (γ : ℝ → C) (t : ℝ) : ι → ℂ :=
  fun j ↦ ∫ s in (0 : ℝ)..t, (θs j).1 ⟨γ s, b3_velocity E C γ s⟩

theorem b3Rest2_continuous_Γ [FiniteDimensional ℂ E] {ι : Type} (θs : ι → b3_HolForm E C)
    {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) : Continuous (b3Rest2_Γ θs γ) :=
  continuous_pi fun j ↦ intervalIntegral.continuous_primitive
    (fun a b ↦ (b3Forms_continuous_holIntegrand (θs j) hγ).intervalIntegrable a b) 0

theorem b3Rest2_Γ_zero {ι : Type} (θs : ι → b3_HolForm E C) (γ : ℝ → C) :
    b3Rest2_Γ θs γ 0 = 0 := by
  funext j; simp [b3Rest2_Γ]

/-- **The Abel–Jacobi map along a path** moves by the class with periods `Γ(t)`. -/
theorem b3Rest2_aj_along [FiniteDimensional ℂ E] (p₀ : C) (h : b3_IsAbelJacobi E C p₀ aj)
    {ι : Type} (bθ : Module.Basis ι ℂ (b3_HolForm E C))
    (L : (ι → ℂ) →ₗ[ℂ] b3Rest2_QJ E C) (hL : L ∘ₗ b3Rest_evalQ bθ = LinearMap.id)
    {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (t : ℝ) :
    ∃ u : ℂ ⊗[ℤ] b3_periodLattice E C,
      b3_cplxPeriod E C u = b3_pathPeriod E C (fun s ↦ γ (t * s)) ∧
      L (b3Rest2_Γ bθ γ t) = Submodule.Quotient.mk u ∧
      aj (γ t) - aj (γ 0) = QuotientAddGroup.mk (Submodule.Quotient.mk u) := by
  have hγt : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun s ↦ γ (t * s)) :=
    hγ.comp (contDiff_const.mul contDiff_id).contMDiff
  obtain ⟨u, hu, hvaj⟩ := h.2 _ hγt
  refine ⟨u, hu, ?_, by simpa using hvaj⟩
  have hT : b3Rest_evalQ bθ (Submodule.Quotient.mk u) = b3Rest2_Γ bθ γ t := by
    funext j
    rw [b3Rest_evalQ_mk, hu, b3Rest2_pathPeriod_scale hγ]
    rfl
  rw [← hT]
  exact LinearMap.congr_fun hL _

set_option maxHeartbeats 400000 in
/-- **The continuous lift of the Abel–Jacobi map along a loop.** -/
theorem b3Rest2_exists_loop_lift [FiniteDimensional ℂ E] (p₀ : C) (h : b3_IsAbelJacobi E C p₀ aj)
    {ι : Type} [Fintype ι] (bθ : Module.Basis ι ℂ (b3_HolForm E C))
    (L : (ι → ℂ) →ₗ[ℂ] b3Rest2_QJ E C) (hL : L ∘ₗ b3Rest_evalQ bθ = LinearMap.id)
    (γ : b3_SmoothLoop E C) (p : C(UnitAddCircle, C)) (hp : ∀ t, γ.1 t = p t) :
    ∃ G : C(unitInterval, b3Rest2_VJ E C), (∀ t : unitInterval,
      b3Rest2_covHom (G t) = aj (p ((t : ℝ) : UnitAddCircle))) ∧
      G 1 - G 0 = b2_coord (b3Rest2_QJ E C) (L (b3Rest2_Γ bθ γ.1 1)) := by
  obtain ⟨v₀, hv₀⟩ := b3Rest2_covHom_spec.2 (aj (p ((0 : ℝ) : UnitAddCircle)))
  obtain ⟨A, hA⟩ : ∃ A : (ι → ℂ) →L[ℂ] b3Rest2_VJ E C,
      ∀ x, A x = b2_coord (b3Rest2_QJ E C) (L x) :=
    ⟨LinearMap.toContinuousLinearMap ((b2_coord (b3Rest2_QJ E C)).toLinearMap ∘ₗ L),
      fun x ↦ rfl⟩
  have hrel : ∀ t : ℝ, b3Rest2_covHom (A (b3Rest2_Γ bθ γ.1 t)) =
      aj (p (t : UnitAddCircle)) - aj (p ((0 : ℝ) : UnitAddCircle)) := by
    intro t
    obtain ⟨u, -, hLu, hu'⟩ := b3Rest2_aj_along aj p₀ h bθ L hL (γ := γ.1) γ.2.2 t
    have e7 : aj (γ.1 t) - aj (γ.1 0) =
        aj (p (t : UnitAddCircle)) - aj (p ((0 : ℝ) : UnitAddCircle)) := by
      rw [hp t, hp 0]
    exact (((congrArg b3Rest2_covHom (hA _)).trans (b3Rest2_covHom_jacMk _ u hLu)).trans
      hu'.symm).trans e7
  have hgen := b3Rest2_exists_loop_lift_gen b3Rest2_covHom aj p (b3Rest2_Γ bθ γ.1)
    (b3Rest2_continuous_Γ bθ γ.2.2) A A.continuous v₀ hv₀ hrel
  obtain ⟨G, hG, hG10⟩ := hgen
  have e9 : b3Rest2_Γ bθ γ.1 1 - b3Rest2_Γ bθ γ.1 0 = b3Rest2_Γ bθ γ.1 1 := by
    simp only [b3Rest2_Γ_zero, sub_zero]
  exact ⟨G, hG, hG10.trans ((map_sub A _ _).symm.trans ((congrArg A e9).trans (hA _)))⟩

/-- **The integration cocycle on a loop is the period.** -/
theorem b3Rest2_integCocycle_loop [FiniteDimensional ℂ E] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] (hE : Module.finrank ℂ E = 1) (p₀ : C) (h : b3_IsAbelJacobi E C p₀ aj)
    (g : ℂ →+ ℂ) (θ : b3_HolForm E C) (γ : b3_SmoothLoop E C) (p : C(UnitAddCircle, C))
    (hp : ∀ t, γ.1 t = p t) :
    (b3Rest2_integCocycle aj haj g θ).1
        (AlgebraicTopology.Simplicial.chainOfSimplex ℂ (loopSimplex p)) =
      g (b3_period E C γ θ) := by
  have : FiniteDimensional ℂ (b3_HolForm E C) := b3A_holForm_finiteDimensional hE
  let bθ := Module.finBasis ℂ (b3_HolForm E C)
  obtain ⟨L, hL⟩ := (b3Rest_evalQ (E := E) (C := C) bθ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (b3Rest_evalQ_injective bθ))
  obtain ⟨G, hG, hG10⟩ := b3Rest2_exists_loop_lift aj p₀ h bθ L hL γ p hp
  obtain ⟨u, hu, hLu, -⟩ := b3Rest2_aj_along aj p₀ h bθ L hL (γ := γ.1) γ.2.2 1
  rw [b3Rest2_integCocycle, b3Rest2_liftCocycle_loop _ _ _ _ _ p G hG, hG10,
    AddMonoidHom.comp_apply, b3Rest2_ellV_coord, hLu]
  show g (b3_cplxPeriod E C u θ) = _
  rw [hu]
  have h1 : (fun s ↦ γ.1 (1 * s)) = γ.1 := by funext s; simp
  rw [h1]
  rfl

end Cocycle

end HodgeLean.Foundations.Program

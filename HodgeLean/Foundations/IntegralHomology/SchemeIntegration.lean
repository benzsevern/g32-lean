import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralPairing

/-! Linearity in the holomorphic form for integral integration pairings.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Manifold
open HodgeLean.Adapters
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem s4_c1a6_integralCocyclePairing_linear (X : TopCat) (c : ℂ)
    (ψ η : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) 1)
    (a : (s4_c1a6_ZChains X).homology 1 ⧸
      Submodule.torsion ℤ ((s4_c1a6_ZChains X).homology 1)) :
    s4_c1a6_integralCocyclePairing X (c • ψ + η) a =
      c * s4_c1a6_integralCocyclePairing X ψ a +
        s4_c1a6_integralCocyclePairing X η a := by
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((s4_c1a6_ZChains X).homologyπ 1)).mp inferInstance h
  rw [s4_c1a6_integralCocyclePairing_cycle,
    s4_c1a6_integralCocyclePairing_cycle, s4_c1a6_integralCocyclePairing_cycle]
  rfl

variable (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
    [ChartedSpace ℂ (ComplexPoint Y)] [IsManifold 𝓘(ℂ, ℂ) ω (ComplexPoint Y)]
    [T2Space (ComplexPoint Y)] [CompactSpace (ComplexPoint Y)]
    [ConnectedSpace (ComplexPoint Y)]
local instance : Module.Finite ℤ (b3_periodLattice ℂ (ComplexPoint Y)) :=
  b3_periodLattice_finite (Module.finrank_self ℂ)
local instance : Module.Free ℤ (b3_periodLattice ℂ (ComplexPoint Y)) :=
  b3_periodLattice_free
local instance : DiscreteTopology
    (b2_latticeMap (b3_periodLattice ℂ (ComplexPoint Y))
      (b3_periodF ℂ (ComplexPoint Y))).range :=
  b2_latticeMap_discrete _ (b3_isWeightOne (Module.finrank_self ℂ))

theorem s4_c1a6_ellV_form_linear (c : ℂ)
    (θ η : b3_HolForm ℂ (ComplexPoint Y)) (v : b3Rest2_VJ ℂ (ComplexPoint Y)) :
    b3Rest2_ellV (c • θ + η) v =
      c * b3Rest2_ellV θ v + b3Rest2_ellV η v := by
  let L := (b3_periodF ℂ (ComplexPoint Y)).liftQ
    (b3_cplxPeriod ℂ (ComplexPoint Y)) le_rfl
  change L ((b2_coord (b3Rest2_QJ ℂ (ComplexPoint Y))).symm v) (c • θ + η) =
    c * L ((b2_coord (b3Rest2_QJ ℂ (ComplexPoint Y))).symm v) θ +
      L ((b2_coord (b3Rest2_QJ ℂ (ComplexPoint Y))).symm v) η
  generalize (b2_coord (b3Rest2_QJ ℂ (ComplexPoint Y))).symm v = w
  induction w using Quotient.inductionOn' with
  | h u => exact b3A_cplxPeriod_mem_linearDual u c θ η

theorem s4_c1a6_integrationCocycle_form_linear
    (aj : ComplexPoint Y → b3_Jacobian ℂ (ComplexPoint Y)) (haj : Continuous aj)
    (c : ℂ) (θ η : b3_HolForm ℂ (ComplexPoint Y)) :
    b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) (c • θ + η) =
      c • b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) θ +
        b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) η := by
  apply Subtype.ext
  apply cochain_ext_simplex_b3Rest2
  intro σ
  simp only [Submodule.coe_add, Submodule.coe_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, b3Rest2_integCocycle,
    b3Rest2_liftCocycle_apply, b3Rest2_LI,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  exact s4_c1a6_ellV_form_linear Y c θ η _

theorem s4_c1a6_integralFormPairing_form_linear
    (aj : ComplexPoint Y → b3_Jacobian ℂ (ComplexPoint Y)) (haj : Continuous aj)
    (c : ℂ) (θ η : b3_HolForm ℂ (ComplexPoint Y)) (a : s4_c1a6_integralLattice Y) :
    s4_c1a6_integralFormPairing Y aj haj (c • θ + η) a =
      c * s4_c1a6_integralFormPairing Y aj haj θ a +
        s4_c1a6_integralFormPairing Y aj haj η a := by
  unfold s4_c1a6_integralFormPairing
  rw [s4_c1a6_integrationCocycle_form_linear Y aj haj]
  exact s4_c1a6_integralCocyclePairing_linear _ _ _ _ _

variable [Module ℂ (GlobalHolomorphicForm Y 1)]

/-- Integration into the dual of scheme forms, using the specified form comparison.
Source: Griffiths–Harris, Principles of Algebraic Geometry, §2.2, integration of holomorphic forms. -/
def s4_c1a6_integralIntegrationMap
    (φ : GlobalHolomorphicForm Y 1 ≃ₗ[ℂ] b3_HolForm ℂ (ComplexPoint Y))
    (aj : ComplexPoint Y → b3_Jacobian ℂ (ComplexPoint Y)) (haj : Continuous aj) :
    s4_c1a6_integralLattice Y →ₗ[ℤ] Module.Dual ℂ (GlobalHolomorphicForm Y 1) where
  toFun a := by
    let f : GlobalHolomorphicForm Y 1 → ℂ :=
      fun θ => s4_c1a6_integralFormPairing Y aj haj (φ θ) a
    have h (c : ℂ) (θ η : GlobalHolomorphicForm Y 1) :
        f (c • θ + η) = c * f θ + f η := by
      dsimp only [f]
      rw [map_add, map_smul]
      exact s4_c1a6_integralFormPairing_form_linear Y aj haj c _ _ a
    have h0 : f 0 = 0 := by
      have hh := h 1 0 0
      simp only [one_smul, add_zero, one_mul] at hh
      linear_combination -hh
    exact
      { toFun := f
        map_add' := fun θ η => by simpa only [one_smul, one_mul] using h 1 θ η
        map_smul' := fun c θ => by
          simpa only [add_zero, h0, mul_zero, smul_eq_mul, RingHom.id_apply] using h c θ 0 }
  map_add' a b := by
    ext θ
    exact map_add (s4_c1a6_integralFormPairing Y aj haj (φ θ)) a b
  map_smul' m a := by
    ext θ
    exact map_smul (s4_c1a6_integralFormPairing Y aj haj (φ θ)) m a

example
    (φ : GlobalHolomorphicForm Y 1 ≃ₗ[ℂ] b3_HolForm ℂ (ComplexPoint Y))
    (aj : ComplexPoint Y → b3_Jacobian ℂ (ComplexPoint Y)) (haj : Continuous aj)
    (a : s4_c1a6_integralLattice Y) (θ : GlobalHolomorphicForm Y 1) :
    s4_c1a6_integralIntegrationMap Y φ aj haj a θ =
      s4_c1a6_integralFormPairing Y aj haj (φ θ) a := rfl

theorem s4_c1a6_integralIntegrationMap_loop
    (φ : GlobalHolomorphicForm Y 1 ≃ₗ[ℂ] b3_HolForm ℂ (ComplexPoint Y))
    (aj : ComplexPoint Y → b3_Jacobian ℂ (ComplexPoint Y)) (haj : Continuous aj)
    (p₀ : ComplexPoint Y) (h : b3_IsAbelJacobi ℂ (ComplexPoint Y) p₀ aj)
    (θ : GlobalHolomorphicForm Y 1) (γ : b3_SmoothLoop ℂ (ComplexPoint Y)) :
    s4_c1a6_integralIntegrationMap Y φ aj haj
      (s4_c1a6_cycleClass Y (s4_c1a6_smoothLoopCycle Y γ)) θ =
        b3_period ℂ (ComplexPoint Y) γ (φ θ) :=
  s4_c1a6_integralFormPairing_loop Y aj haj p₀ h (φ θ) γ

end HodgeLean.Foundations.Program

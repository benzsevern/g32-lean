import HodgeLean.Foundations.IntegralHomology.StageThree.Proofs

/-! General integral period evaluation, its naturality, and normalized surface comparisons.
Implication from the explicit manifold and selected form data only.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Manifold
open HodgeLean.Foundations.Program HodgeLean.Adapters
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.IntegralHomology.StageThree

/-- Pairing coboundary.
Source: Hatcher, Algebraic Topology, §3.1, evaluation on cycles. -/
theorem pairing_coboundary (S : ShortComplex (ModuleCat ℤ)) (u v : S.X₂ →ₗ[ℤ] ℂ)
    (hu : u.comp S.f.hom = (0 : S.X₁ →ₗ[ℤ] ℂ)) (hv : v.comp S.f.hom = (0 : S.X₁ →ₗ[ℤ] ℂ))
    (b : S.X₃ →ₗ[ℤ] ℂ) (h : v - u = b.comp S.g.hom) :
    pairing S u hu = pairing S v hv :=
  pairing_coboundary_aux S u v hu hv b h

example (S : ShortComplex (ModuleCat ℤ)) (u : S.X₂ →ₗ[ℤ] ℂ)
    (hu : u.comp S.f.hom = (0 : S.X₁ →ₗ[ℤ] ℂ)) (z : S.cycles) :
    pairing S u hu (Submodule.Quotient.mk (S.homologyπ z)) = u (S.iCycles z) :=
  s4_c1a6_boundaryTorsionDesc_cycle S u hu z

/-- Pairing natural.
Source: Hatcher, Algebraic Topology, §3.1, the Kronecker pairing. -/
theorem pairing_natural (S T : ShortComplex (ModuleCat ℤ)) (f : S ⟶ T)
    (u : T.X₂ →ₗ[ℤ] ℂ) (hu : u.comp T.f.hom = (0 : T.X₁ →ₗ[ℤ] ℂ))
    (hv : (u.comp f.τ₂.hom).comp S.f.hom = (0 : S.X₁ →ₗ[ℤ] ℂ))
    (a : S.homology ⧸ Submodule.torsion ℤ S.homology) :
    pairing S (u.comp f.τ₂.hom) hv a =
      pairing T u hu (torsionQuotientMap (ShortComplex.homologyMap f).hom a) :=
  pairing_natural_aux S T f u hu hv a

example (S T : ShortComplex (ModuleCat ℤ)) (f : S ⟶ T)
    (u : T.X₂ →ₗ[ℤ] ℂ) (hv : (u.comp f.τ₂.hom).comp S.f.hom = (0 : S.X₁ →ₗ[ℤ] ℂ))
    (z : S.cycles) :
    pairing S (u.comp f.τ₂.hom) hv (Submodule.Quotient.mk (S.homologyπ z)) =
      u (f.τ₂ (S.iCycles z)) :=
  s4_c1a6_boundaryTorsionDesc_cycle S _ hv z

/-- Cocycle natural.
Source: Hatcher, Algebraic Topology, §3.1; C1a6IntegralCoefficients. -/
theorem cocycle_natural (X Y : TopCat.{0}) (f : X ⟶ Y)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj Y) (1 : ℕ))
    (η : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) (1 : ℕ))
    (hη : η.val = ψ.val.comp
      ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℂ ℂ)).f (1 : ℕ)).hom)
    (a : Lattice X) :
    cocyclePairing X η a = cocyclePairing Y ψ (mapLattice f a) :=
  cocycle_natural_aux X Y f ψ η hη a

example (X : TopCat.{0})
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) (1 : ℕ))
    (z : (ZChains X).cycles (1 : ℕ)) :
    cocyclePairing X ψ (Submodule.Quotient.mk ((ZChains X).homologyπ (1 : ℕ) z)) =
      ψ.val (s4_c1a6_zToCChainGroup X (1 : ℕ) ((ZChains X).iCycles (1 : ℕ) z)) :=
  s4_c1a6_integralCocyclePairing_cycle X ψ z

/-- Surface bridge.
Source: Forster, Lectures on Riemann Surfaces, §§19–21; Hatcher, §3.1; b3Rest2_integCocycle_loop. -/
theorem surface_bridge {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (hE : Module.finrank ℂ E = (1 : ℕ)) (p₀ : C)
    (aj : C → b3_Jacobian E C) (haj : Continuous aj)
    (h : b3_IsAbelJacobi E C p₀ aj) :
    ∃ e : Lattice (TopCat.of C) ≃ₗ[ℤ] b3_periodLattice E C,
      (∀ (a : Lattice (TopCat.of C)) (θ : b3_HolForm E C),
        surfacePeriod (e a) θ = cocyclePairing (TopCat.of C)
          (b3Rest2_integCocycle aj haj (AddMonoidHom.id ℂ) θ) a) ∧
      (∀ γ : b3_SmoothLoop E C,
        e (Submodule.Quotient.mk ((ZChains (TopCat.of C)).homologyπ (1 : ℕ)
          (((ZChains (TopCat.of C)).sc (1 : ℕ)).moduleCatCyclesIso.inv
            (loopCycle ℤ (b3Rest2_circ γ))))) = b3_latticePeriod E C γ) :=
  surface_bridge_aux hE p₀ aj haj h

example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.val = b3_ellipticA) (hb : b.val = b3_ellipticB) :
    ∃ θ : b3_HolForm b3_EllipticModel b3_Elliptic, (surfacePeriod (E := b3_EllipticModel) (C := b3_Elliptic)) (b3_latticePeriod b3_EllipticModel b3_Elliptic a) θ = (1 : ℂ) ∧
      (surfacePeriod (E := b3_EllipticModel) (C := b3_Elliptic)) (b3_latticePeriod b3_EllipticModel b3_Elliptic b) θ = Complex.I :=
  b3_elliptic_periods a b ha hb

/-- Scheme bridge.
Source: Forster, §21; C1a6IntegralMap and its specified scheme-form comparison. -/
theorem scheme_bridge (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
    [Module ℂ (GlobalHolomorphicForm Y (1 : ℕ))]
    [ChartedSpace ℂ (ComplexPoint Y)] [IsManifold 𝓘(ℂ, ℂ) ω (ComplexPoint Y)]
    [T2Space (ComplexPoint Y)] [CompactSpace (ComplexPoint Y)]
    [ConnectedSpace (ComplexPoint Y)]
    [Module.Finite ℤ (b3_periodLattice ℂ (ComplexPoint Y))]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice ℂ (ComplexPoint Y))
      (b3_periodF ℂ (ComplexPoint Y))).range]
    (φ : GlobalHolomorphicForm Y (1 : ℕ) ≃ₗ[ℂ] b3_HolForm ℂ (ComplexPoint Y))
    (p₀ : ComplexPoint Y) (aj : ComplexPoint Y → b3_Jacobian ℂ (ComplexPoint Y))
    (haj : Continuous aj) (h : b3_IsAbelJacobi ℂ (ComplexPoint Y) p₀ aj) :
    ∃ e : Lattice (TopCat.of (ComplexPoint Y)) ≃ₗ[ℤ]
        b3_periodLattice ℂ (ComplexPoint Y),
      s4_c1a6_integralIntegrationMap Y φ aj haj =
        (transport surfacePeriod φ).comp e.toLinearMap ∧
      (∀ γ : b3_SmoothLoop ℂ (ComplexPoint Y),
        e (s4_c1a6_cycleClass Y (s4_c1a6_smoothLoopCycle Y γ)) =
          b3_latticePeriod ℂ (ComplexPoint Y) γ) :=
  scheme_bridge_aux Y φ p₀ aj haj h

example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.val = b3_ellipticA) (hb : b.val = b3_ellipticB) :
    ∃ θ : b3_HolForm b3_EllipticModel b3_Elliptic, transport (surfacePeriod (E := b3_EllipticModel) (C := b3_Elliptic)) (LinearEquiv.neg ℂ) (b3_latticePeriod b3_EllipticModel b3_Elliptic a) θ = -(1 : ℂ) := by
  have hp := b3_elliptic_periods a b ha hb
  rcases hp with ⟨θ, hθ, _⟩
  refine ⟨θ, ?_⟩
  change (surfacePeriod (E := b3_EllipticModel) (C := b3_Elliptic)) (b3_latticePeriod b3_EllipticModel b3_Elliptic a) (-θ) = -(1 : ℂ)
  rw [map_neg]
  exact congrArg Neg.neg hθ

/-- Period image.
Source: Forster, §21; b3_periodLattice_free, b3_periodLattice_finite, b3_finrank_periodLattice. -/
theorem period_image {E C F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [AddCommGroup F] [Module ℂ F]
    (hE : Module.finrank ℂ E = (1 : ℕ)) (φ : F ≃ₗ[ℂ] b3_HolForm E C) :
    Function.Injective (transport surfacePeriod φ) ∧
      Module.Finite ℤ (transport surfacePeriod φ).range ∧
      Module.Free ℤ (transport surfacePeriod φ).range ∧
      Module.finrank ℤ (transport surfacePeriod φ).range = (2 : ℕ) * Module.finrank ℂ F :=
  period_image_aux hE φ

example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.val = b3_ellipticA) (hb : b.val = b3_ellipticB) :
    ∃ θ : b3_HolForm b3_EllipticModel b3_Elliptic, (surfacePeriod (E := b3_EllipticModel) (C := b3_Elliptic)) (b3_latticePeriod b3_EllipticModel b3_Elliptic a) θ ≠
      (surfacePeriod (E := b3_EllipticModel) (C := b3_Elliptic)) (b3_latticePeriod b3_EllipticModel b3_Elliptic b) θ := by
  have hp := b3_elliptic_periods a b ha hb
  rcases hp with ⟨θ, hθ, hη⟩
  refine ⟨θ, ?_⟩
  change b3_period _ _ a θ ≠ b3_period _ _ b θ
  rw [hθ, hη]
  intro h
  have := congrArg Complex.im h
  norm_num at this

/-- Complex period.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 2.2; b3_range_cplxPeriod. -/
theorem complex_period {E C F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [AddCommGroup F] [Module ℂ F]
    (hE : Module.finrank ℂ E = (1 : ℕ)) (φ : F ≃ₗ[ℂ] b3_HolForm E C) :
    Function.Surjective (LinearMap.liftBaseChange ℂ (transport surfacePeriod φ)) ∧
      LinearMap.ker (LinearMap.liftBaseChange ℂ (transport surfacePeriod φ)) =
        b3_periodF E C ∧
      (∀ (v : ℂ ⊗[ℤ] b3_periodLattice E C) (θ : F),
        LinearMap.liftBaseChange ℂ (transport surfacePeriod φ) v θ =
          b3_cplxPeriod E C v (φ θ)) :=
  complex_period_aux hE φ

example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.val = b3_ellipticA) (hb : b.val = b3_ellipticB) :
    ∃ θ : b3_HolForm b3_EllipticModel b3_Elliptic, LinearMap.liftBaseChange ℂ (surfacePeriod (E := b3_EllipticModel) (C := b3_Elliptic))
      (((1 : ℂ) / (2 : ℂ)) ⊗ₜ[ℤ] b3_latticePeriod b3_EllipticModel b3_Elliptic a) θ = (1 : ℂ) / (2 : ℂ) := by
  have hp := b3_elliptic_periods a b ha hb
  rcases hp with ⟨θ, hθ, _⟩
  refine ⟨θ, ?_⟩
  rw [LinearMap.liftBaseChange_tmul]
  change ((1 : ℂ) / (2 : ℂ)) * b3_period _ _ a θ = (1 : ℂ) / (2 : ℂ)
  rw [hθ, mul_one]

end HodgeLean.Foundations.IntegralHomology.StageThree

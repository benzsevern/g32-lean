import HodgeLean.Foundations.Program.CurveJacobianAEllipticAJ
import HodgeLean.Foundations.Program.CurveJacobianAFunctor
import HodgeLean.Foundations.Program.CurveJacobianAPlane
import HodgeLean.Foundations.Program.CurveJacobianACrossings
import HodgeLean.Foundations.Program.CurveJacobianAFiniteDim
import HodgeLean.Foundations.Program.CurveJacobianA2Intersection
import HodgeLean.Foundations.Program.CurveJacobianDefs
import HodgeLean.Foundations.Program.CurveJacobianFormsLattice
import HodgeLean.Foundations.Program.CurveJacobianRestAJ
import HodgeLean.Foundations.Program.CurveJacobianRestPoly
import HodgeLean.Foundations.Program.CurveJacobianRestUnique
import HodgeLean.Foundations.Program.CurveJacobianRest2Key
import HodgeLean.Foundations.Program.CurveJacobianRest2Riemann
import HodgeLean.Foundations.Program.CurveJacobianRest2Singular
import HodgeLean.Foundations.Program.CurveJacobianUnimodMain
import HodgeLean.Foundations.Program.CurveJacobianSideAdjoint

set_option maxHeartbeats 400000

/-! # Track B3, compact Riemann surfaces and their Jacobians: proofs

One `_aux` theorem per statement of the frozen `CurveJacobian.lean`; the bodies are open.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold HodgeLean.Adapters AlgebraicTopology.Singular
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-! ## Holomorphic forms and the period lattice -/

theorem b3_holForm_finiteDimensional_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    FiniteDimensional ℂ (b3_HolForm E C) := by
  exact b3A_holForm_finiteDimensional hE

theorem b3_complexPlane_not_finiteDimensional_aux :
    ¬ FiniteDimensional ℂ (b3_HolForm ℂ ℂ) := by
  exact b3A_complexPlane_not_finiteDimensional

theorem b3_period_mem_linearDual_aux (γ : b3_SmoothLoop E C) :
    b3_period E C γ ∈ b3_linearDual E C := by
  exact b3A_pathPeriod_linear γ.1 γ.2.2

theorem b3_periodLattice_free_aux [Module.Finite ℤ (b3_periodLattice E C)] :
    Module.Free ℤ (b3_periodLattice E C) := by
  exact b3A_periodLattice_free

theorem b3_periodLattice_finite_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    Module.Finite ℤ (b3_periodLattice E C) :=
  b3Forms_periodLattice_finite hE

theorem b3_finrank_periodLattice_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    Module.finrank ℤ (b3_periodLattice E C) = 2 * Module.finrank ℂ (b3_HolForm E C) := by
  haveI : FiniteDimensional ℂ E := Module.finite_of_finrank_pos (by omega)
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  exact b3Rest2_finrank_eq hE (b3Rest2_key hE)

theorem b3_finrank_cohomology_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    Module.finrank ℚ (Cohomology ℚ (TopCat.of C) 1) = 2 * Module.finrank ℂ (b3_HolForm E C) := by
  haveI : FiniteDimensional ℂ E := Module.finite_of_finrank_pos (by omega)
  exact b3Rest2_finrank_cohomology hE

theorem b3_range_cplxPeriod_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    LinearMap.range (b3_cplxPeriod E C) = b3_linearDual E C := by
  exact b3A_range_cplxPeriod hE

theorem b3_isWeightOne_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    b2_IsWeightOne (b3_periodLattice E C) (b3_periodF E C) := by
  haveI : FiniteDimensional ℂ E := Module.finite_of_finrank_pos (by omega)
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  exact b3Rest2_isWeightOne hE (b3Rest2_key hE)

/-! ## Comparison with singular cohomology -/

theorem b3_period_eq_iff_loopPeriod_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (γ δ : b3_SmoothLoop E C) (p q : C(UnitAddCircle, C))
    (hp : ∀ t : ℝ, γ.1 t = p t) (hq : ∀ t : ℝ, δ.1 t = q t) :
    b3_period E C γ = b3_period E C δ ↔ loopPeriod p = loopPeriod q := by
  haveI : FiniteDimensional ℂ E := Module.finite_of_finrank_pos (by omega)
  exact b3Rest2_period_eq_iff_loopPeriod hE γ δ p q hp hq

theorem b3_exists_smoothLoop_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (_hE : Module.finrank ℂ E = 1) (p : C(UnitAddCircle, C)) :
    ∃ (γ : b3_SmoothLoop E C) (q : C(UnitAddCircle, C)),
      (∀ t : ℝ, γ.1 t = q t) ∧ loopPeriod q = loopPeriod p :=
  b3Rest_exists_smoothLoop p

/-! ## Intersection numbers and the Riemann bilinear relations -/

section Intersection

theorem b3_crossings_finite_aux [FiniteDimensional ℂ E] [T2Space C]
    (_hE : Module.finrank ℂ E = 1)
    (γ δ : b3_SmoothLoop E C)
    (h : b3_Transverse E γ δ) :
    (b3_crossings E γ δ).Finite := by
  exact b3A_crossings_finite γ δ h

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3_intersection_antisymm_aux [IsManifold 𝓘(ℂ, E) ω C] [FiniteDimensional ℂ E] (γ δ : b3_SmoothLoop E C) :
    b3_intersection E δ γ = -b3_intersection E γ δ := by
  exact b3A_intersection_antisymm γ δ

theorem b3_exists_intersectionForm_aux [FiniteDimensional ℂ E]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    ∃ Q : LinearMap.BilinForm ℤ (b3_periodLattice E C), b3_IsIntersectionForm E Q := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  exact ⟨b3Rest2_QZ hE (b3Rest2_key hE), b3Rest2_isIntersectionForm hE (b3Rest2_key hE)⟩

theorem b3_intersectionForm_unique_aux [FiniteDimensional ℂ E]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (Q Q' : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQ : b3_IsIntersectionForm E Q) (hQ' : b3_IsIntersectionForm E Q') :
    Q = Q' :=
  b3Rest_intersectionForm_unique hE Q Q' hQ hQ'

theorem b3_intersectionForm_isRiemannForm_aux [FiniteDimensional ℂ E]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQ : b3_IsIntersectionForm E Q) :
    b2_IsRiemannForm (b3_periodLattice E C) (b3_periodF E C) Q := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  exact b3Rest2_isRiemannForm hE (b3Rest2_key hE) Q hQ

theorem b3_intersectionForm_bijective_aux [FiniteDimensional ℂ E]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQ : b3_IsIntersectionForm E Q) :
    Function.Bijective Q :=
  b3Unimod_intersectionForm_bijective hE Q hQ

end Intersection

/-! ## The Abel–Jacobi map -/

theorem b3_exists_abelJacobi_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (p₀ : C) :
    ∃ aj : C → b3_Jacobian E C, b3_IsAbelJacobi E C p₀ aj := by
  exact b3A_exists_abelJacobi hE p₀

theorem b3_abelJacobi_unique_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (_hE : Module.finrank ℂ E = 1) (p₀ : C) (aj aj' : C → b3_Jacobian E C)
    (h : b3_IsAbelJacobi E C p₀ aj) (h' : b3_IsAbelJacobi E C p₀ aj') :
    aj = aj' := by
  exact b3A_abelJacobi_unique p₀ aj aj' h h'

theorem b3_abelJacobi_holomorphic_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (p₀ : C) (aj : C → b3_Jacobian E C) (h : b3_IsAbelJacobi E C p₀ aj) :
    ContMDiff 𝓘(ℂ, E)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)) → ℂ) ω aj :=
  b3Rest_abelJacobi_holomorphic hE p₀ aj h

/-! ## Functoriality -/

section Maps

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {C' : Type} [TopologicalSpace C'] [ChartedSpace E' C'] [IsManifold 𝓘(ℂ, E') ω C']

theorem b3_pullback_mem_holForm_aux (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (θ : TangentBundle 𝓘(ℂ, E') C' → ℂ) (hθ : θ ∈ b3_HolForm E' C') :
    b3_pullback E E' f θ ∈ b3_HolForm E C := by
  exact b3A_pullback_mem_holForm f hf θ hθ

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω C'] in
theorem b3_pathIntegral_comp_aux [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω C']
    (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (θ : TangentBundle 𝓘(ℂ, E') C' → ℂ) :
    b3_pathIntegral E' C' (f ∘ γ) θ = b3_pathIntegral E C γ (b3_pullback E E' f θ) := by
  exact b3A_pathIntegral_comp f hf γ hγ θ

theorem b3_exists_pushforward_aux (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) :
    ∃ g : b3_periodLattice E C →+ b3_periodLattice E' C', b3_IsPushforward E E' f g ∧
      b3_periodF E C ≤ (b3_periodF E' C').comap (b2_cplxMap g) := by
  exact b3A_exists_pushforward f hf

theorem b3_pushforward_unique_aux (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (g g' : b3_periodLattice E C →+ b3_periodLattice E' C')
    (hg : b3_IsPushforward E E' f g) (hg' : b3_IsPushforward E E' f g') :
    g = g' := by
  exact b3A_pushforward_unique f hf g g' hg hg'

theorem b3_exists_pullbackLattice_aux [FiniteDimensional ℂ E] [FiniteDimensional ℂ E']
    [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    [T2Space C'] [CompactSpace C'] [ConnectedSpace C'] (hE' : Module.finrank ℂ E' = 1)
    (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (g : b3_periodLattice E C →+ b3_periodLattice E' C') (hg : b3_IsPushforward E E' f g)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)) (hQ : b3_IsIntersectionForm E Q)
    (Q' : LinearMap.BilinForm ℤ (b3_periodLattice E' C')) (hQ' : b3_IsIntersectionForm E' Q') :
    ∃ h : b3_periodLattice E' C' →+ b3_periodLattice E C,
      (∀ a b, Q (h a) b = Q' a (g b)) ∧
        b3_periodF E' C' ≤ (b3_periodF E C).comap (b2_cplxMap h) := by
  letI : Module.Finite ℤ (b3_periodLattice E C) := b3_periodLattice_finite_aux hE
  letI : Module.Free ℤ (b3_periodLattice E C) := b3_periodLattice_free_aux
  have hQbij := b3_intersectionForm_bijective_aux hE Q hQ
  obtain ⟨h, hadj⟩ :=
    CurveJacobianSide_exists_adjoint Q hQbij Q' g.toIntLinearMap
  obtain ⟨g₀, hg₀, hg₀F⟩ := b3A_exists_pushforward f hf
  have hgg₀ : g = g₀ := b3A_pushforward_unique f hf g g₀ hg hg₀
  have hgF : b3_periodF E C ≤ (b3_periodF E' C').comap (b2_cplxMap g) := by
    rwa [hgg₀]
  refine ⟨h, hadj, ?_⟩
  exact CurveJacobianSide_adjoint_preserves_filtration
    (b3_periodF E C) (b3_periodF E' C') Q Q'
    (b3_isWeightOne_aux hE) (b3_intersectionForm_isRiemannForm_aux hE Q hQ)
    (b3_intersectionForm_isRiemannForm_aux hE' Q' hQ') g h hgF hadj

theorem b3_abelJacobi_natural_aux
    [T2Space C] [CompactSpace C] [ConnectedSpace C] (_hE : Module.finrank ℂ E = 1)
    [T2Space C'] [CompactSpace C'] [ConnectedSpace C'] (_hE' : Module.finrank ℂ E' = 1)
    (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (g : b3_periodLattice E C →+ b3_periodLattice E' C') (hg : b3_IsPushforward E E' f g)
    (hgF : b3_periodF E C ≤ (b3_periodF E' C').comap (b2_cplxMap g))
    (p₀ : C) (aj : C → b3_Jacobian E C) (haj : b3_IsAbelJacobi E C p₀ aj)
    (aj' : C' → b3_Jacobian E' C') (haj' : b3_IsAbelJacobi E' C' (f p₀) aj') (p : C) :
    aj' (f p) = b2_torusHom (b3_periodF E C) (b3_periodF E' C') g hgF (aj p) := by
  exact b3A_abelJacobi_natural f hf g hg hgF p₀ aj haj aj' haj' p

end Maps

/-! ## The elliptic curve -/

theorem b3_elliptic_connectedSpace_aux : ConnectedSpace b3_Elliptic := by
  exact b3A_elliptic_connectedSpace

theorem b3_elliptic_finrank_holForm_aux :
    Module.finrank ℂ (b3_HolForm b3_EllipticModel b3_Elliptic) = 1 := by
  exact b3A_elliptic_finrank_holForm

theorem b3_elliptic_abelJacobi_bijective_aux
    (aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic)
    (h : b3_IsAbelJacobi b3_EllipticModel b3_Elliptic 0 aj) :
    Function.Bijective aj := by
  exact b3A_elliptic_abelJacobi_bijective aj h

/-! ## Explicit loops of the elliptic curve -/

theorem b3_ellipticA_contMDiff_aux :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, b3_EllipticModel) 1 b3_ellipticA := by
  exact b3A_ellipticA_contMDiff

theorem b3_ellipticB_contMDiff_aux :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, b3_EllipticModel) 1 b3_ellipticB := by
  exact b3A_ellipticB_contMDiff

theorem b3_elliptic_periods_aux (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    ∃ θ : b3_HolForm b3_EllipticModel b3_Elliptic,
      b3_period _ _ a θ = 1 ∧ b3_period _ _ b θ = Complex.I := by
  exact b3A_elliptic_periods a b ha hb

theorem b3_elliptic_transverse_aux (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    b3_Transverse b3_EllipticModel a b := by
  exact b3A_elliptic_transverse a b ha hb

theorem b3_elliptic_intersection_aux (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    b3_intersection b3_EllipticModel a b = 1 := by
  exact b3A_elliptic_intersection a b ha hb

theorem b3_elliptic_intersectionForm_eq_aux (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ : b3_IsIntersectionForm b3_EllipticModel Q)
    (Q' : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ'alt : ∀ x, Q' x x = 0)
    (hQ'ab : Q' (b3_latticePeriod _ _ a) (b3_latticePeriod _ _ b) = 1) :
    Q = Q' := by
  have ea : a = b3A_loopA := Subtype.ext ha
  have eb : b = b3A_loopB := Subtype.ext hb
  subst a
  subst b
  exact CurveJacobianA2_elliptic_intersectionForm_eq Q hQ Q' hQ'alt hQ'ab

theorem b3_elliptic_abelJacobi_apply_aux (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB)
    (aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic)
    (h : b3_IsAbelJacobi b3_EllipticModel b3_Elliptic 0 aj) (s t : ℝ) :
    aj (b3_ellipticPoint s t) = QuotientAddGroup.mk (Submodule.Quotient.mk
      ((s : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ a + (t : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ b)) := by
  exact b3A_elliptic_abelJacobi_apply a b ha hb aj h s t

end HodgeLean.Foundations.Program

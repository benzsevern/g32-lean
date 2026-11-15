import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric

/-! # Intermediate normalization and invariant descent
Implications from finite morphisms, generic-field embeddings and categorical
quotient properties. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Integral-field chart maps agree under restriction.
Source: Hartshorne, Algebraic Geometry, II.3 (regular functions on integral schemes). -/
theorem s2e_step1_integral_maps_restrict_aux
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (f : X ⟶ Y) (U V : Y.left.Opens) (hVU : V ≤ U)
    [Nonempty (f.left ⁻¹ᵁ U)] [Nonempty (f.left ⁻¹ᵁ V)]
    (K : Type) [Field K] [Algebra Γ(Y.left, U) K] [Algebra Γ(Y.left, V) K]
    (κ : K →+* X.left.functionField)
    (ρ : integralClosure Γ(Y.left, U) K →+* integralClosure Γ(Y.left, V) K)
    (hρ : ∀ a, (ρ a : K) = (a : K))
    (jU : integralClosure Γ(Y.left, U) K →+* Γ(X.left, f.left ⁻¹ᵁ U))
    (jV : integralClosure Γ(Y.left, V) K →+* Γ(X.left, f.left ⁻¹ᵁ V))
    (hjU : ∀ a, algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField (jU a) = κ a)
    (hjV : ∀ a, algebraMap Γ(X.left, f.left ⁻¹ᵁ V) X.left.functionField (jV a) = κ a) :
    ∀ a, (X.left.presheaf.map (homOfLE (show f.left ⁻¹ᵁ V ≤ f.left ⁻¹ᵁ U from
      fun _ hx => hVU hx)).op).hom (jU a) = jV (ρ a) := by
  intro a
  apply X.left.germToFunctionField_injective (f.left ⁻¹ᵁ V)
  change X.left.presheaf.germ _ _ _ ((X.left.presheaf.map _).hom (jU a)) = _
  rw [X.left.presheaf.germ_res_apply]
  exact (hjU a).trans ((congrArg κ (hρ a)).symm.trans (hjV (ρ a)).symm)

/-- Local intermediate integral-field maps give a global factor.
Source: Hartshorne, Algebraic Geometry, II.3, normalization construction;
Mathlib AlgebraicGeometry/Normalization.lean, normalizationGlueData. -/
theorem s2e_step1_normalization_glue_aux
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left]
    (K : CommRingCat) (hK : IsField K) (κ : K ⟶ X.left.functionField)
    (η : Spec K ⟶ Y.left) [QuasiCompact η] [QuasiSeparated η]
    (hη : Spec.map κ ≫ η =
      X.left.fromSpecStalk (genericPoint X.left) ≫ f.left) :
    ∃ g : X.left ⟶ η.normalization,
      g ≫ η.fromNormalization = f.left ∧
      X.left.fromSpecStalk (genericPoint X.left) ≫ g =
        Spec.map κ ≫ η.toNormalization := by
  apply s2e_step1_integralTarget_lift X Y f η.normalization η.fromNormalization
    (Spec.map κ ≫ η.toNormalization)
  rw [Category.assoc, η.toNormalization_fromNormalization, hη]

/-- The intermediate factor is finite and surjective.
Source: Atiyah--Macdonald, Introduction to Commutative Algebra, Theorem 5.10;
Hartshorne, Algebraic Geometry, II.3 (finite morphisms). -/
theorem s2e_step1_normalization_factor_finite_surjective_aux
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left]
    (K : CommRingCat) (hK : IsField K) (κ : K ⟶ X.left.functionField)
    (η : Spec K ⟶ Y.left) [QuasiCompact η] [QuasiSeparated η]
    (hη : Spec.map κ ≫ η =
      X.left.fromSpecStalk (genericPoint X.left) ≫ f.left)
    (g : X.left ⟶ η.normalization)
    (hfac : g ≫ η.fromNormalization = f.left)
    (hgen : X.left.fromSpecStalk (genericPoint X.left) ≫ g =
      Spec.map κ ≫ η.toNormalization) :
    IsFinite g ∧ Surjective g := by
  haveI : IsFinite (g ≫ η.fromNormalization) := by rw [hfac]; infer_instance
  haveI : IsFinite g := IsFinite.of_comp g η.fromNormalization
  letI : Field K := hK.toField
  haveI : Surjective (Spec.map κ) := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap κ.hom)
    intro x
    exact ⟨default, Subsingleton.elim _ _⟩
  haveI : IsDominant (X.left.fromSpecStalk (genericPoint X.left) ≫ g) := by
    rw [hgen]
    infer_instance
  haveI : IsDominant g := IsDominant.of_comp
    (X.left.fromSpecStalk (genericPoint X.left)) g
  exact ⟨inferInstance, surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range⟩

/-- Generic fixed-field compatibility forces invariance of the factor.
Source: Hartshorne, Algebraic Geometry, II.4, separatedness and dense agreement. -/
theorem s2e_step1_normalization_factor_invariant_aux
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left]
    (K : CommRingCat) (hK : IsField K) (κ : K ⟶ X.left.functionField)
    (η : Spec K ⟶ Y.left) [QuasiCompact η] [QuasiSeparated η]
    (hη : Spec.map κ ≫ η =
      X.left.fromSpecStalk (genericPoint X.left) ≫ f.left)
    (g : X.left ⟶ η.normalization)
    (hfac : g ≫ η.fromNormalization = f.left)
    (hgen : X.left.fromSpecStalk (genericPoint X.left) ≫ g =
      Spec.map κ ≫ η.toNormalization)
    (u : X ⟶ X) (τ : Spec X.left.functionField ⟶ Spec X.left.functionField)
    (hu : u ≫ f = f)
    (hτ : X.left.fromSpecStalk (genericPoint X.left) ≫ u.left =
      τ ≫ X.left.fromSpecStalk (genericPoint X.left))
    (hκ : τ ≫ Spec.map κ = Spec.map κ) :
    u.left ≫ g = g := by
  haveI := s2e_step1_generic_dominant X.left
  refine ext_of_isDominant_of_isSeparated η.fromNormalization ?_
    (X.left.fromSpecStalk (genericPoint X.left)) ?_
  · rw [Category.assoc, hfac]
    exact congrArg Over.Hom.left hu
  · rw [← Category.assoc, hτ, Category.assoc, hgen,
      ← Category.assoc, hκ]

/-- Invariant regular functions descend along the retained finite quotient.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, 3rd ed.,
Chapter 1, section 1 (finite-group quotients). -/
theorem s2e_step1_invariant_affine_descent_aux
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (b : Γ(X.left, q.left ⁻¹ᵁ U))
    (hb : ∀ u, ((a u).left.appLE (q.left ⁻¹ᵁ U) (q.left ⁻¹ᵁ U)
      (by change q.left ⁻¹ᵁ U ≤ ((a u).left ≫ q.left) ⁻¹ᵁ U
          have he : (a u).left ≫ q.left = q.left := congrArg Over.Hom.left (hinv u)
          rw [he])).hom b = b) :
    ∃! c : Γ(Y.left, U), (q.left.app U).hom c = b := by
  letI : ∀ u, IsIso (a u) := s2e_step1_action_isIso X G a ha1 hamul
  exact s2e_step1_invariant_sections X Y G a q hinv hquot U hU b hb

/-- Finite categorical quotient fibres on complex points are group orbits.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, 3rd ed.,
Chapter 1, section 1 (finite-group quotients). -/
theorem s2e_step1_finite_quotient_point_orbits_aux
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (x y : ComplexPoint X) (hxy : Point.map q x = Point.map q y) :
    ∃ u : G, Point.map (a u) x = y := by
  classical
  letI : ∀ u, IsIso (a u) := s2e_step1_action_isIso X G a ha1 hamul
  let z : Spec ↧ℂ := IsLocalRing.closedPoint ℂ
  let b0 := q.left (x.left z)
  let U : Y.left.Opens := (Y.left.affineCover.f (Y.left.affineCover.idx b0)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  let W := q.left ⁻¹ᵁ U
  have hx : ⊤ ≤ x.left ⁻¹ᵁ W :=
    s2e_step1_point_preimage X x W (Y.left.affineCover.covers b0)
  have hy : ⊤ ≤ y.left ⁻¹ᵁ W := by
    apply s2e_step1_point_preimage X y W
    have he : x.left ≫ q.left = y.left ≫ q.left := congrArg Over.Hom.left hxy
    have he' := congrArg (fun t : Spec ↧ℂ ⟶ Y.left => t z) he
    change q.left (x.left z) = q.left (y.left z) at he'
    change q.left (y.left z) ∈ U
    rw [← he']
    exact Y.left.affineCover.covers b0
  have hW : IsAffineOpen W := hU.preimage q.left
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  let φ : Γ(X.left, W) →ₐ[ℂ] ℂ := s2e_step1_pointEvaluation X W x hx
  let ψ : Γ(X.left, W) →ₐ[ℂ] ℂ := s2e_step1_pointEvaluation X W y hy
  by_contra hno
  have hneval : ¬ ∃ u : G, ∀ r : Γ(X.left, W), ψ r = φ (u • r) := by
    rintro ⟨u, hu⟩
    apply hno
    have hpre := s2e_step1_action_preimage X Y q (a u⁻¹) (hinv u⁻¹) U
    have hux : ⊤ ≤ (Point.map (a u⁻¹) x).left ⁻¹ᵁ W := by
      change ⊤ ≤ x.left ⁻¹ᵁ ((a u⁻¹).left ⁻¹ᵁ W)
      intro t _
      exact hpre (hx trivial)
    refine ⟨u⁻¹, s2e_step1_point_ext_on_affine X W hW _ y hux hy ?_⟩
    apply AlgHom.ext
    intro r
    rw [s2e_step1_pointEvaluation_map X W (a u⁻¹) hpre x hx hux r]
    exact (hu r).symm
  obtain ⟨r, hr, hsep⟩ := s2e_invariant_separates_evaluation_orbits φ ψ hneval
  have hr' : ∀ u, ((a u).left.appLE W W
      (s2e_step1_action_preimage X Y q (a u) (hinv u) U)).hom r = r := by
    intro u
    have he := hr u⁻¹
    change ((a (u⁻¹)⁻¹).left.appLE W W _).hom r = r at he
    simpa only [inv_inv] using he
  obtain ⟨c, hc, -⟩ := s2e_step1_invariant_sections X Y G a q hinv hquot U hU r hr'
  apply hsep
  rw [← hc]
  exact s2e_step1_pointEvaluation_base X Y q U x y hx hy hxy c

/-- The retained symmetric quotient separates permutation orbits.
Source: Schoen (1988), p. 13, symmetric product construction;
Mumford--Fogarty--Kirwan, Geometric Invariant Theory, Chapter 1, section 1. -/
theorem s2e_step1_retained_symmetric_orbits_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (N : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hinv : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : HodgeLean.Adapters.g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! w : B ⟶ T, γ ≫ w = v)
    (x y : ComplexPoint (HodgeLean.Adapters.g3_power Z N))
    (hxy : Point.map γ x = Point.map γ y) :
    ∃ σ, Point.map (s2_permute Z N σ) x = y := by
  haveI : Surjective γ.left :=
    s2e_step1_surjective_of_complexPoint_surjective (HodgeLean.Adapters.g3_power Z N) B γ hsurj
  exact s2e_step1_finite_quotient_point_orbits_aux
    (HodgeLean.Adapters.g3_power Z N) B (Equiv.Perm (Fin N))
    (s2_permute Z N) (s2e_step1_permute_one Z N) (s2e_step1_permute_mul Z N)
    γ hinv hquot x y hxy

end HodgeLean.Foundations.Program

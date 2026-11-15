import HodgeLean.Foundations.Program.SchoenCycleStep1Proofs

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
theorem s2e_step1_integral_maps_restrict
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
      fun _ hx => hVU hx)).op).hom (jU a) = jV (ρ a) :=
  s2e_step1_integral_maps_restrict_aux X Y f U V hVU K κ ρ hρ jU jV hjU hjV

example
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
      fun _ hx => hVU hx)).op).hom (jU a) = jV (ρ a) :=
  s2e_step1_integral_maps_restrict X Y f U V hVU K κ ρ hρ jU jV hjU hjV

/-- Local intermediate integral-field maps give a global factor.
Source: Hartshorne, Algebraic Geometry, II.3, normalization construction;
Mathlib AlgebraicGeometry/Normalization.lean, normalizationGlueData. -/
theorem s2e_step1_normalization_glue
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left]
    (K : CommRingCat) (hK : IsField K) (κ : K ⟶ X.left.functionField)
    (η : Spec K ⟶ Y.left) [QuasiCompact η] [QuasiSeparated η]
    (hη : Spec.map κ ≫ η =
      X.left.fromSpecStalk (genericPoint X.left) ≫ f.left) :
    ∃ g : X.left ⟶ η.normalization,
      g ≫ η.fromNormalization = f.left ∧
      X.left.fromSpecStalk (genericPoint X.left) ≫ g =
        Spec.map κ ≫ η.toNormalization :=
  s2e_step1_normalization_glue_aux X Y f K hK κ η hη

example
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left]
    (K : CommRingCat) (hK : IsField K) (κ : K ⟶ X.left.functionField)
    (η : Spec K ⟶ Y.left) [QuasiCompact η] [QuasiSeparated η]
    (hη : Spec.map κ ≫ η =
      X.left.fromSpecStalk (genericPoint X.left) ≫ f.left) :
    ∃ g : X.left ⟶ η.normalization,
      g ≫ η.fromNormalization = f.left ∧
      X.left.fromSpecStalk (genericPoint X.left) ≫ g =
        Spec.map κ ≫ η.toNormalization :=
  s2e_step1_normalization_glue X Y f K hK κ η hη

/-- The intermediate factor is finite and surjective.
Source: Atiyah--Macdonald, Introduction to Commutative Algebra, Theorem 5.10;
Hartshorne, Algebraic Geometry, II.3 (finite morphisms). -/
theorem s2e_step1_normalization_factor_finite_surjective
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
    IsFinite g ∧ Surjective g :=
  s2e_step1_normalization_factor_finite_surjective_aux X Y f K hK κ η hη g hfac hgen

example
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
    IsFinite g ∧ Surjective g :=
  s2e_step1_normalization_factor_finite_surjective X Y f K hK κ η hη g hfac hgen

/-- Generic fixed-field compatibility forces invariance of the factor.
Source: Hartshorne, Algebraic Geometry, II.4, separatedness and dense agreement. -/
theorem s2e_step1_normalization_factor_invariant
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
    u.left ≫ g = g :=
  s2e_step1_normalization_factor_invariant_aux X Y f K hK κ η hη g hfac hgen u τ hu hτ hκ

example
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
    u.left ≫ g = g :=
  s2e_step1_normalization_factor_invariant X Y f K hK κ η hη g hfac hgen u τ hu hτ hκ

/-- Invariant regular functions descend along the retained finite quotient.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, 3rd ed.,
Chapter 1, section 1 (finite-group quotients). -/
theorem s2e_step1_invariant_affine_descent
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
    ∃! c : Γ(Y.left, U), (q.left.app U).hom c = b :=
  s2e_step1_invariant_affine_descent_aux X Y G a ha1 hamul q hinv hquot U hU b hb

example
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
    ∃! c : Γ(Y.left, U), (q.left.app U).hom c = b :=
  s2e_step1_invariant_affine_descent X Y G a ha1 hamul q hinv hquot U hU b hb

/-- Finite categorical quotient fibres on complex points are group orbits.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, 3rd ed.,
Chapter 1, section 1 (finite-group quotients). -/
theorem s2e_step1_finite_quotient_point_orbits
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
    ∃ u : G, Point.map (a u) x = y :=
  s2e_step1_finite_quotient_point_orbits_aux X Y G a ha1 hamul q hinv hquot x y hxy

example
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
    ∃ u : G, Point.map (a u) x = y :=
  s2e_step1_finite_quotient_point_orbits X Y G a ha1 hamul q hinv hquot x y hxy

/-- The retained symmetric quotient separates permutation orbits.
Source: Schoen (1988), p. 13, symmetric product construction;
Mumford--Fogarty--Kirwan, Geometric Invariant Theory, Chapter 1, section 1. -/
theorem s2e_step1_retained_symmetric_orbits
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (N : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hinv : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : HodgeLean.Adapters.g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! w : B ⟶ T, γ ≫ w = v)
    (x y : ComplexPoint (HodgeLean.Adapters.g3_power Z N))
    (hxy : Point.map γ x = Point.map γ y) :
    ∃ σ, Point.map (s2_permute Z N σ) x = y :=
  s2e_step1_retained_symmetric_orbits_aux Z B N γ hsurj hinv hquot x y hxy

example
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (N : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hinv : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : HodgeLean.Adapters.g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! w : B ⟶ T, γ ≫ w = v)
    (x y : ComplexPoint (HodgeLean.Adapters.g3_power Z N))
    (hxy : Point.map γ x = Point.map γ y) :
    ∃ σ, Point.map (s2_permute Z N σ) x = y :=
  s2e_step1_retained_symmetric_orbits Z B N γ hsurj hinv hquot x y hxy

end HodgeLean.Foundations.Program

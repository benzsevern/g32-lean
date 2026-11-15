import HodgeLean.Foundations.Program.SchoenTowerI1aPreDefs
import Mathlib.AlgebraicGeometry.Gluing

/-! # Section actions for invariant charts
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Inverse pullback gives a group action on the section ring.
Source: SGA 1, Exposé V, §1. -/
theorem s2v_i1alo_section_action
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) :
    ∃ ρ : MulSemiringAction G Γ(X.left, U),
      (∀ g r, @SMul.smul G Γ(X.left, U) ρ.toSMul g r =
        ((a g⁻¹).left.appLE U U (hiU g⁻¹)).hom r) ∧
      (letI := ρ
       letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
       Algebra.IsInvariant (s2v_i1a_chartInvariants X G a U hiU) Γ(X.left, U) G) := by
  let ρ : MulSemiringAction G Γ(X.left, U) :=
    { smul g r := ((a g⁻¹).left.appLE U U (hiU g⁻¹)).hom r
      one_smul := by
        intro r
        change ((a (1 : G)⁻¹).left.appLE U U _).hom r = r
        simp only [inv_one, ha1, Over.id_left]
        simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
        change (X.left.presheaf.map (𝟙 (Opposite.op U))).hom r = r
        rw [CategoryTheory.Functor.map_id]
        rfl
      mul_smul := by
        intro g h r
        change ((a (g * h)⁻¹).left.appLE U U _).hom r =
          (((a h⁻¹).left.appLE U U _) ≫ ((a g⁻¹).left.appLE U U _)).hom r
        rw [Scheme.Hom.appLE_comp_appLE]
        simp only [mul_inv_rev, hamul, Over.comp_left]
      smul_zero g := map_zero _
      smul_add g r s := map_add _ _ _
      smul_one g := map_one _
      smul_mul g r s := map_mul _ _ _ }
  refine ⟨ρ, fun _ _ => rfl, ?_⟩
  letI := ρ
  letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
  constructor
  intro r hr
  refine ⟨⟨r, fun g => ?_⟩, rfl⟩
  specialize hr g⁻¹
  change ((a (g⁻¹)⁻¹).left.appLE U U _).hom r = r at hr
  simpa only [inv_inv] using hr

/-- Finite-type section generators and the invariant action give module finiteness.
Source: SGA 1, Exposé V, §1; Mathlib, Algebra.IsInvariant.isIntegral. -/
theorem s2v_i1alo_section_finite
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (ρ : MulSemiringAction G Γ(X.left, U))
    (hρ : ∀ g r, @SMul.smul G Γ(X.left, U) ρ.toSMul g r =
      ((a g⁻¹).left.appLE U U (hiU g⁻¹)).hom r)
    (hI : letI := ρ
      letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
      Algebra.IsInvariant (s2v_i1a_chartInvariants X G a U hiU) Γ(X.left, U) G) :
    letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
    Module.Finite (s2v_i1a_chartInvariants X G a U hiU) Γ(X.left, U) := by
  let A := s2v_i1a_chartInvariants X G a U hiU
  let c := X.hom.appLE ⊤ U (by simp)
  have hc (r : Γ(Spec ↧ℂ, ⊤)) : c.hom r ∈ A := by
    intro g
    change (((X.hom.appLE ⊤ U _) ≫ (a g).left.appLE U U _).hom r) = _
    erw [Scheme.Hom.appLE_comp_appLE]
    simp only [Over.w]
    rfl
  let cA : Γ(Spec ↧ℂ, ⊤) →+* A := c.hom.codRestrict A hc
  have hfin : A.subtype.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := cA)
    exact X.hom.finiteType_appLE (isAffineOpen_top _) hU (by simp)
  letI := ρ
  letI := A.subtype.toAlgebra
  letI : Algebra.IsInvariant A Γ(X.left, U) G := hI
  letI : Algebra.IsIntegral A Γ(X.left, U) := Algebra.IsInvariant.isIntegral A _ G
  letI : Algebra.FiniteType A Γ(X.left, U) := hfin
  exact Algebra.IsIntegral.finite

/-- Preserved prime opens have open images under the invariant spectrum map.
Source: SGA 1, Exposé V, §1; Mathlib, Algebra.IsInvariant.exists_smul_of_under_eq. -/
theorem s2v_i1alo_invariant_spectrum_image
    (A B G : Type) [CommRing A] [CommRing B] [Group G] [Finite G]
    [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    (hinj : Function.Injective (algebraMap A B))
    (N : TopologicalSpace.Opens (PrimeSpectrum B))
    (hN : ∀ (g : G) (P Q : PrimeSpectrum B),
      Q.asIdeal = g • P.asIdeal → P ∈ N → Q ∈ N) :
    ∃ W : TopologicalSpace.Opens (PrimeSpectrum A),
      (W : Set (PrimeSpectrum A)) = PrimeSpectrum.comap (algebraMap A B) '' N ∧
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' (W : Set (PrimeSpectrum A)) = N := by
  let f := PrimeSpectrum.comap (algebraMap A B)
  have hs : f ⁻¹' (f '' (N : Set (PrimeSpectrum B))) = N := by
    ext P
    constructor
    · rintro ⟨Q, hQ, he⟩
      have he' : Q.asIdeal.under A = P.asIdeal.under A := congrArg PrimeSpectrum.asIdeal he
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G Q.asIdeal P.asIdeal he'
      exact hN g Q P hg hQ
    · intro hP
      exact ⟨P, hP, rfl⟩
  have hi : (algebraMap A B).IsIntegral := (Algebra.IsInvariant.isIntegral A B G).1
  have hq := (PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hi).isQuotientMap
    (PrimeSpectrum.continuous_comap _) (hi.comap_surjective hinj)
  have hopen : IsOpen (f '' (N : Set (PrimeSpectrum B))) := by
    rw [← hq.isOpen_preimage, hs]
    exact N.isOpen
  exact ⟨⟨_, hopen⟩, rfl, hs⟩

/-- Restriction of sections preserves the fixed subrings on nested invariant opens.
Source: SGA 1, Exposé V, §1, naturality of section pullback. -/
theorem s2v_i1alo_invariant_restriction
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U V : X.left.Opens) (hVU : V ≤ U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) :
    ∃ f : s2v_i1a_chartInvariants X G a U hiU →+*
        s2v_i1a_chartInvariants X G a V hiV,
      ∀ t, (f t).val = (X.left.presheaf.map (homOfLE hVU).op).hom t.val := by
  let r := X.left.presheaf.map (homOfLE hVU).op
  have hr (t : s2v_i1a_chartInvariants X G a U hiU) :
      r.hom t.val ∈ s2v_i1a_chartInvariants X G a V hiV := by
    intro g
    have h : r ≫ (a g).left.appLE V V (hiV g) =
        (a g).left.appLE U U (hiU g) ≫ r := by
      dsimp [r]
      rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
    change (r ≫ (a g).left.appLE V V (hiV g)).hom t.val = r.hom t.val
    rw [h]
    change r.hom (((a g).left.appLE U U (hiU g)).hom t.val) = r.hom t.val
    rw [t.property g]
  exact ⟨(r.hom.comp (s2v_i1a_chartInvariants X G a U hiU).subtype).codRestrict _ hr,
    fun _ => rfl⟩

end HodgeLean.Foundations.Program

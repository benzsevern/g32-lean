import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Defs
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Localization.FractionRing

/-! # Reduced inverse images under smooth morphisms

HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters TopologicalSpace
namespace AlgebraicGeometry.SingularCycles

open scoped TensorProduct in
/-- Flat unramified finite-type algebras over a domain are reduced.
Source: Mathlib, Algebra.FormallyUnramified.isReduced_of_field and flat scalar extension. -/
theorem flat_unramified_reduced_domain
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] [Module.Flat R A] [Algebra.FormallyUnramified R A] : _root_.IsReduced A := by
  let K := FractionRing R
  have : _root_.IsReduced (K ⊗[R] A) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

/-- Smooth algebras over a domain are reduced.
Source: Mathlib, Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial. -/
theorem smooth_reduced_domain
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] : _root_.IsReduced A := by
  constructor
  intro x hx
  apply eq_zero_of_localization x
  intro p hp
  letI := hp
  obtain ⟨f, hf, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  letI := hAlg
  letI := hTower
  letI := hEtale
  have : _root_.IsReduced (Localization.Away f) :=
    flat_unramified_reduced_domain (MvPolynomial (Fin n) R) _
  have hz := (hx.map (algebraMap A (Localization.Away f))).eq_zero
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f)
    (Localization.Away f) x).mp hz
  obtain ⟨k, hk⟩ := m.property
  apply (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) x).mpr
  refine ⟨⟨m, ?_⟩, hm⟩
  change (m : A) ∉ p
  rw [← hk]
  exact p.primeCompl.pow_mem hf k

/-- A smooth scheme over an integral base is reduced.
Source: EGA IV, 17.5.1; the affine localization argument in CycleClassFlatComparisonProofs. -/
theorem smooth_reduced_integral {X Y : Scheme} (f : X ⟶ Y)
    [IsIntegral Y] [Smooth f] : AlgebraicGeometry.IsReduced X := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, _⟩ := Smooth.exists_isStandardSmooth f x
  have : Nonempty U := ⟨⟨f x, e hxV⟩⟩
  algebraize [(f.appLE U V e).hom]
  have : Algebra.Smooth Γ(Y, U) Γ(X, V) := by
    rw [← RingHom.smooth_algebraMap]
    exact f.smooth_appLE hU hV e
  have : _root_.IsReduced Γ(X, V) := smooth_reduced_domain Γ(Y, U) Γ(X, V)
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  exact isReduced_localizationPreserves (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) inferInstance

/-- The scheme-theoretic inverse image of a prime under a smooth map is reduced.
Source: Fulton, Intersection Theory, second edition, §1.7; smooth base change. -/
theorem inverseIdeal_isReduced {X Z : Scheme}
    (f : X ⟶ Z) [Smooth f] (x : Z) :
    IsReduced (ccm3_inverseIdeal f x).subscheme := by
  have : IsIntegral (ccm3_primeIdeal Z x).subscheme :=
    inferInstanceAs (IsIntegral (cycleComponent Z x))
  have : IsReduced (CategoryTheory.Limits.pullback f
      (ccm3_primeIdeal Z x).subschemeι) :=
    smooth_reduced_integral (CategoryTheory.Limits.pullback.snd _ _)
  exact ObjectProperty.prop_of_iso (fun Y : Scheme => IsReduced Y)
    ((ccm3_primeIdeal Z x).comapIso f).symm inferInstance

end AlgebraicGeometry.SingularCycles

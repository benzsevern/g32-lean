import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2_fixedRing_normal (B G : Type*) [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Group G] [MulSemiringAction G B] :
    IsIntegrallyClosed (FixedPoints.subring B G) := by
  let R := FixedPoints.subring B G
  let K := FractionRing B
  let f : FractionRing R →ₐ[R] K := IsFractionRing.liftAlgHom
    (g := Algebra.ofId R K)
    ((IsFractionRing.injective B K).comp Subtype.val_injective)
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  intro x hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    ((hx.map f).tower_top : IsIntegral B (f x))
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbB : (b : B) ≠ 0 := by
    intro hz
    exact hb0 (Subtype.ext hz)
  have habK : algebraMap B K (a : B) / algebraMap B K (b : B) = algebraMap B K y := by
    have he := congrArg f hab
    rw [map_div₀, f.commutes, f.commutes, ← hy] at he
    exact he
  have hyb : y * (b : B) = (a : B) := by
    apply IsFractionRing.injective B K
    rw [map_mul]
    exact ((div_eq_iff (map_ne_zero_of_mem_nonZeroDivisors (algebraMap B K)
      (IsFractionRing.injective B K) (mem_nonZeroDivisors_of_ne_zero hbB))).mp habK).symm
  have hyfix : ∀ g : G, g • y = y := by
    intro g
    apply mul_right_cancel₀ hbB
    calc
      (g • y) * (b : B) = g • (y * (b : B)) := by
        rw [smul_mul', b.property g]
      _ = (a : B) := by rw [hyb, a.property g]
      _ = y * (b : B) := hyb.symm
  refine ⟨⟨y, hyfix⟩, ?_⟩
  apply f.injective
  exact (f.commutes ⟨y, hyfix⟩).trans hy

theorem s2_fixedAlgebra_finite (R B G : Type*) [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.FiniteType R B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B] :
    Module.Finite (FixedPoints.subalgebra R B G) B := by
  have : Algebra.IsIntegral (FixedPoints.subalgebra R B G) B :=
    Algebra.IsInvariant.isIntegral _ _ G
  have : Algebra.FiniteType (FixedPoints.subalgebra R B G) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ B
  exact Algebra.IsIntegral.finite

open AlgebraicGeometry in
theorem s2_fixedAlgebra_spec_finite (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.FiniteType R B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B] :
    IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap (FixedPoints.subalgebra R B G) B))) := by
  rw [IsFinite.SpecMap_iff]
  change Module.Finite (FixedPoints.subalgebra R B G) B
  exact s2_fixedAlgebra_finite R B G

open AlgebraicGeometry in
theorem s2_fixedAlgebra_spec_surjective (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G R B] :
    Function.Surjective (Spec.map (CommRingCat.ofHom
      (algebraMap (FixedPoints.subalgebra R B G) B))) := by
  have : Algebra.IsIntegral (FixedPoints.subalgebra R B G) B :=
    Algebra.IsInvariant.isIntegral _ _ G
  exact Algebra.IsIntegral.comap_surjective (FixedPoints.subalgebra R B G) B

open AlgebraicGeometry in
theorem s2_fixedRing_spec_stalk_normal (B G : Type) [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Group G] [MulSemiringAction G B]
    (x : Spec (CommRingCat.of (FixedPoints.subring B G))) :
    IsIntegrallyClosed ((Spec (CommRingCat.of (FixedPoints.subring B G))).presheaf.stalk x) := by
  let R := FixedPoints.subring B G
  let x' : PrimeSpectrum R := x
  have : x'.asIdeal.IsPrime := x'.isPrime
  have : IsIntegrallyClosed R := s2_fixedRing_normal B G
  have : IsIntegrallyClosed (Localization.AtPrime x'.asIdeal) :=
    isIntegrallyClosed_of_isLocalization _ x'.asIdeal.primeCompl
      (le_nonZeroDivisors_of_noZeroDivisors (by simp))
  exact IsIntegrallyClosed.of_equiv (StructureSheaf.stalkIso R x').toRingEquiv

open scoped Pointwise in
open AlgebraicGeometry in
theorem s2_fixedAlgebra_spec_fibres (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G R B] (x y : PrimeSpectrum B) :
    PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B) x =
      PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B) y ↔
      ∃ g : G, y.asIdeal = g • x.asIdeal := by
  constructor
  · intro hxy
    exact Algebra.IsInvariant.exists_smul_of_under_eq
      (FixedPoints.subalgebra R B G) B G x.asIdeal y.asIdeal
      (congrArg PrimeSpectrum.asIdeal hxy)
  · rintro ⟨g, hg⟩
    apply PrimeSpectrum.ext
    change x.asIdeal.under (FixedPoints.subalgebra R B G) =
      y.asIdeal.under (FixedPoints.subalgebra R B G)
    rw [hg, Ideal.under_smul]

end HodgeLean.Foundations.Program

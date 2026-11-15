import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.NormalizationCoefficientSlice
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientCoordinates
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.BinomialPrimitiveScalar
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.EtaleChartNormality
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineSliceProjection
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

section
variable {R K L : Type} [CommRing R] [Algebra ℂ R] [Field K] [Field L]
variable (u v : R)
local notation "A" => RegularPairChart.ring u v

/-- The actual original slice retains canonical integral selector and parameter evaluations for its specified field generator. -/
theorem normalization_slice_binomial_coordinates
    [IsDomain A] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra ℂ L] [IsScalarTower ℂ A L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (ε : R) (hε : IsUnit ε)
    (N : ℕ) (cE : MvPolynomial (Fin N) ℂ →ₐ[ℂ] A) (hcE : cE.toRingHom.Etale)
    (a : Fin N) (ha : cE (MvPolynomial.X a) = RegularPairChart.ratio u v)
    (m α : ℕ) (hm : 0 < m) (hdegree : Module.finrank K L = m)
    (w : L) (hw0 : w ≠ 0)
    (hw : w ^ m = algebraMap A L (RegularPairChart.coeff u v ε) *
      (algebraMap A L (RegularPairChart.ratio u v)) ^ α)
    (hgen : Subfield.closure (Set.range (algebraMap A L) ∪ {w}) = ⊤)
    (hs : algebraMap A L (RegularPairChart.ratio u v) ≠ 0)
    (δ : L ≃ₐ[K] L) (ho : orderOf δ = m)
    (X B : Over (Spec ↧ℂ)) [IsSeparated B.hom] [IsSeparated X.hom]
    (η : Spec ↧L ⟶ X.left) [QuasiCompact η] [QuasiSeparated η]
    [CompactSpace (ComplexPoint (s2b_normalizationOver X η))]
    [CompactSpace (ComplexPoint X)] [T2Space (ComplexPoint X)]
    (b : X ⟶ B) (x : ComplexPoint B)
    (j : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ X) [IsOpenImmersion j.left]
    (hF : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ j.left = η)
    (c : Over.mk (ComplexPoint.affineSpecStructureMap R) ⟶ B) [Mono c]
    (hj : j ≫ b = Over.homMk
      (Spec.map (CommRingCat.ofHom (regularPairCoefficientAlgHom u v).toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap (regularPairCoefficientAlgHom u v)) ≫ c)
    (φ : R →ₐ[ℂ] ℂ) (hx : Point.map c ((ComplexPoint.affineSpecEquiv R).symm φ) = x)
    (hβ : Function.Surjective (Point.map (s2b_normalizationMap X η)))
    (D : X.left.IdealSheafData) (vE : ComplexPoint (exceptionalSlice b x) ≃ₜ OnePoint ℂ)
    (hendpoint : ∀ z : ComplexPoint (exceptionalSlice b x),
      (Point.map (pullback.fst b x) z).left (IsLocalRing.closedPoint ℂ) ∈ D.support ↔ vE z = ∞)
    (hchart : ∀ z : ComplexPoint (coveringSlice (s2b_normalizationMap X η) b x),
      (Point.map (pullback.fst b x) (Point.map (sliceProjection (s2b_normalizationMap X η) b x) z)).left
        (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left ↔
      (Point.map (pullback.fst b x) (Point.map (sliceProjection (s2b_normalizationMap X η) b x) z)).left
        (IsLocalRing.closedPoint ℂ) ∉ D.support)
    (hcoordinate : ∀ (z : ComplexPoint (exceptionalSlice b x))
        (y : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap A))),
      Point.map j y = Point.map (pullback.fst b x) z →
        vE z = ((ComplexPoint.affineSpecEquiv A y (RegularPairChart.ratio u v) : ℂ) : OnePoint ℂ)) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ m ∧ δ w = algebraMap ℂ L ζ * w ∧
    ∃ (q t : integralClosure A L) (κ : ℂ)
      (E : integralCoefficientFibre (L := L) (regularPairCoefficientAlgHom u v) φ ≃ₜ
        ZMod (Nat.gcd m α) × ℂ),
      (q : L) = w ^ (m / Nat.gcd m α) /
        (algebraMap A L (RegularPairChart.ratio u v)) ^ (α / Nat.gcd m α) ∧
      (t : L) = (algebraMap A L (RegularPairChart.ratio u v)) ^
        Nat.gcdA (m / Nat.gcd m α) (α / Nat.gcd m α) *
        w ^ Nat.gcdB (m / Nat.gcd m α) (α / Nat.gcd m α) ∧
      κ ^ Nat.gcd m α = φ ε ∧ κ ≠ 0 ∧
      (∀ l : ZMod (Nat.gcd m α),
        (κ * (ζ ^ (m / Nat.gcd m α)) ^ l.val) ^
          (-Nat.gcdB (m / Nat.gcd m α) (α / Nat.gcd m α)) ≠ 0) ∧
      ∀ x, x.val q = κ * (ζ ^ (m / Nat.gcd m α)) ^ (E x).1.val ∧
        x.val t = (E x).2 ∧
        x.val (algebraMap A (integralClosure A L) (RegularPairChart.ratio u v)) =
          (κ * (ζ ^ (m / Nat.gcd m α)) ^ (E x).1.val) ^
            (-Nat.gcdB (m / Nat.gcd m α) (α / Nat.gcd m α)) *
              (E x).2 ^ (m / Nat.gcd m α) := by
  let β := s2b_normalizationMap X η
  let P := sliceProjection β b x
  let T := {z : ComplexPoint (coveringSlice β b x) //
    (Point.map (pullback.fst b x) (Point.map P z)).left (IsLocalRing.closedPoint ℂ) ∉ D.support}
  obtain ⟨H, hH⟩ := normalization_coefficient_slice_homeomorph X B η b x j hF
    (regularPairCoefficientAlgHom u v) c hj φ hx
  let HC : {z : ComplexPoint (coveringSlice β b x) //
      (Point.map (pullback.fst b x) (Point.map P z)).left (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left} ≃ₜ T :=
    (Homeomorph.refl _).subtype hchart
  let Q : integralCoefficientFibre (L := L) (regularPairCoefficientAlgHom u v) φ ≃ₜ T := H.trans HC
  let ev : integralCoefficientFibre (L := L) (regularPairCoefficientAlgHom u v) φ → ℂ :=
    fun z => z.val (algebraMap A (integralClosure A L) (RegularPairChart.ratio u v))
  have hQ (z) : vE (Point.map P (Q z).val) = ((ev z : ℂ) : OnePoint ℂ) := by
    obtain ⟨y, hy, hyev⟩ := hH z
    have h := hcoordinate (Point.map P (H z).val) y hy
    rw [hyev] at h
    exact h
  obtain ⟨p, hp, hps, hpc⟩ := affine_slice_projection_proper_surjective β b x hβ D vE hendpoint
  have hev : ev = p ∘ Q := by
    funext z
    apply OnePoint.coe_injective
    exact (hQ z).symm.trans (hpc (Q z)).symm
  have hproper : IsProperMap ev := by
    rw [hev]
    exact hp.comp Q.isProperMap
  have hsurj : Function.Surjective ev := by
    rw [hev]
    exact hps.comp Q.surjective
  letI : IsIntegrallyClosed A := etale_complex_chart_integrally_closed N cE hcE
  let δA := δ.restrictScalars A
  have hoA : orderOf δA = m :=
    (orderOf_injective (AlgEquiv.restrictScalarsHom A) (AlgEquiv.restrictScalars_injective A) δ).trans ho
  obtain ⟨ζ, hζ, heig⟩ := generating_binomial_primitive_complex_scalar δA m hm hoA w hw0
    (RegularPairChart.coeff u v ε * RegularPairChart.ratio u v ^ α)
    (by simpa only [map_mul, map_pow] using hw) hgen
  refine ⟨ζ, hζ, heig, ?_⟩
  exact integral_coefficient_binomial_coordinates u v φ ε hε
    N cE hcE a ha m α hm δ hdegree ho ζ hζ w hw hgen heig hs hproper hsurj

end
end AlgebraicGeometry.RamifiedNormalization.StageFour

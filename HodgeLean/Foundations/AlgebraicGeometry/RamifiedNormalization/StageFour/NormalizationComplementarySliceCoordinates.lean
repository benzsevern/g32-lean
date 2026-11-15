import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.NormalizationSliceCoordinates

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

/-- Complementary original binomial exponents retain the same gcd label type in the actual integral coefficient classification. -/
theorem normalization_complementary_slice_binomial_coordinates
    [IsDomain A] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra ℂ L] [IsScalarTower ℂ A L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (ε : R) (hε : IsUnit ε)
    (N : ℕ) (cE : MvPolynomial (Fin N) ℂ →ₐ[ℂ] A) (hcE : cE.toRingHom.Etale)
    (a : Fin N) (ha : cE (MvPolynomial.X a) = RegularPairChart.ratio u v)
    (m α : ℕ) (hm : 0 < m) (hα : α ≤ m) (hdegree : Module.finrank K L = m)
    (w : L) (hw0 : w ≠ 0)
    (hw : w ^ m = algebraMap A L (RegularPairChart.coeff u v ε) *
      (algebraMap A L (RegularPairChart.ratio u v)) ^ (m - α))
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
        (algebraMap A L (RegularPairChart.ratio u v)) ^ ((m - α) / Nat.gcd m α) ∧
      (t : L) = (algebraMap A L (RegularPairChart.ratio u v)) ^
        Nat.gcdA (m / Nat.gcd m α) ((m - α) / Nat.gcd m α) *
        w ^ Nat.gcdB (m / Nat.gcd m α) ((m - α) / Nat.gcd m α) ∧
      κ ^ Nat.gcd m α = φ ε ∧ κ ≠ 0 ∧
      (∀ l : ZMod (Nat.gcd m α),
        (κ * (ζ ^ (m / Nat.gcd m α)) ^ l.val) ^
          (-Nat.gcdB (m / Nat.gcd m α) ((m - α) / Nat.gcd m α)) ≠ 0) ∧
      ∀ x, x.val q = κ * (ζ ^ (m / Nat.gcd m α)) ^ (E x).1.val ∧
        x.val t = (E x).2 ∧
        x.val (algebraMap A (integralClosure A L) (RegularPairChart.ratio u v)) =
          (κ * (ζ ^ (m / Nat.gcd m α)) ^ (E x).1.val) ^
            (-Nat.gcdB (m / Nat.gcd m α) ((m - α) / Nat.gcd m α)) *
              (E x).2 ^ (m / Nat.gcd m α) := by
  have hdata := normalization_slice_binomial_coordinates u v ε hε
    N cE hcE a ha m (m - α) hm hdegree w hw0 hw hgen hs δ ho
    X B η b x j hF c hj φ hx hβ D vE hendpoint hchart hcoordinate
  rw [Nat.gcd_self_sub_right hα] at hdata
  exact hdata

end
end AlgebraicGeometry.RamifiedNormalization.StageFour

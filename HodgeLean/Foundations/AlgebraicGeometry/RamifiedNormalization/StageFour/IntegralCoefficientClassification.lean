import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientInertia
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientOrbits
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.NormalizedEvaluationClassification

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

section
variable {R K L : Type} [CommRing R] [Algebra ℂ R] [Field K] [Field L]
variable (u v : R)
local notation "A" => RegularPairChart.ring u v

/-- The normalized coefficient fibre of a single etale binomial chart exhausts the labelled complex lines, deriving its orbit and inertia data from the original field. -/
theorem integral_coefficient_binomial_homeomorph
    [IsDomain A] [IsIntegrallyClosed A]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra ℂ L] [IsScalarTower ℂ A L]
    [FiniteDimensional K L] [IsGalois K L]
    (φ : R →ₐ[ℂ] ℂ) (ε : R) (hε : IsUnit ε)
    (N : ℕ) (cE : MvPolynomial (Fin N) ℂ →ₐ[ℂ] A) (hcE : cE.toRingHom.Etale)
    (j : Fin N) (hj : cE (MvPolynomial.X j) = RegularPairChart.ratio u v)
    (m α : ℕ) (hm : 0 < m)
    (δ : L ≃ₐ[K] L) (hdegree : Module.finrank K L = m) (horder : orderOf δ = m)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (w : L)
    (hw : w ^ m = algebraMap A L (RegularPairChart.coeff u v ε) *
      (algebraMap A L (RegularPairChart.ratio u v)) ^ α)
    (hgen : Subfield.closure (Set.range (algebraMap A L) ∪ {w}) = ⊤)
    (hδw : δ w = algebraMap ℂ L ζ * w)
    (hs : algebraMap A L (RegularPairChart.ratio u v) ≠ 0)
    (hproper : IsProperMap (fun x : integralCoefficientFibre (L := L)
        (regularPairCoefficientAlgHom u v) φ =>
      x.val (algebraMap A (integralClosure A L) (RegularPairChart.ratio u v))))
    (hsurj : Function.Surjective (fun x : integralCoefficientFibre (L := L)
        (regularPairCoefficientAlgHom u v) φ =>
      x.val (algebraMap A (integralClosure A L) (RegularPairChart.ratio u v)))) :
    ∃ (E : integralCoefficientFibre (L := L) (regularPairCoefficientAlgHom u v) φ ≃ₜ
        ZMod (Nat.gcd m α) × ℂ) (k : ZMod (Nat.gcd m α) → ℂ),
      (∀ l, k l ≠ 0) ∧ ∀ x,
        x.val (algebraMap A (integralClosure A L) (RegularPairChart.ratio u v)) =
          k (E x).1 * (E x).2 ^ (m / Nat.gcd m α) := by
  let F : A →+* L := algebraMap A L
  let f := regularPairCoefficientAlgHom u v
  let X := integralCoefficientFibre (L := L) f φ
  let δA := δ.restrictScalars A
  let D := integralCoefficientFibreDeck f φ δA
  let ev : X → (normalizedChart F →+* ℂ) := fun x => x.val.toRingHom
  have hwint : w ∈ normalizedChart F := by
    change _root_.IsIntegral A w
    apply IsIntegral.of_pow hm
    rw [hw, ← map_pow, ← map_mul]
    exact isIntegral_algebraMap
  let wN : normalizedChart F := ⟨w, hwint⟩
  have hwN : wN ^ m = StageTwo.integralCoeff F
      (f ε * RegularPairChart.ratio u v ^ α) := by
    apply Subtype.ext
    change w ^ m = F (f ε * RegularPairChart.ratio u v ^ α)
    change w ^ m = algebraMap A L
      (RegularPairChart.coeff u v ε * RegularPairChart.ratio u v ^ α)
    rw [map_mul, map_pow]
    exact hw
  let c : normalizedChart F := StageTwo.integralCoeff F (algebraMap ℂ A ζ)
  have hc : IsUnit c := ((hζ.isUnit (Nat.ne_of_gt hm)).map (algebraMap ℂ A)).map
    (StageTwo.integralCoeff F)
  have hsσ : δA.toRingEquiv (F (RegularPairChart.ratio u v)) = F (RegularPairChart.ratio u v) :=
    δA.commutes _
  have hwσ : δA.toRingEquiv (wN : L) = (c : L) * (wN : L) := by
    change δ w = F (algebraMap ℂ A ζ) * w
    rw [← IsScalarTower.algebraMap_apply ℂ A L ζ]
    exact hδw
  have hε0 : φ ε ≠ 0 := (hε.map φ.toRingHom).ne_zero
  have hεev (x : X) : ev x (StageTwo.integralCoeff F (f ε)) = φ ε := x.property ε
  have hcev (x : X) : ev x c = ζ := by
    change x.val (algebraMap A (integralClosure A L) (algebraMap ℂ A ζ)) = ζ
    rw [← IsScalarTower.algebraMap_apply ℂ A (integralClosure A L) ζ]
    exact x.val.commutes ζ
  have heval (x : X) (b : normalizedChart F) : ev (D x) b = ev x (δA.mapIntegralClosure b) := rfl
  have hcont (b : normalizedChart F) : Continuous (fun x : X => ev x b) :=
    (ComplexPoint.continuous_affineAlgebraHom_apply (integralClosure A L) b).comp continuous_subtype_val
  have horbit := integral_coefficient_ratio_fibre_orbit u v φ δ (horder.trans hdegree.symm)
  have hδm : δ ^ m = 1 := horder ▸ pow_orderOf_eq_one δ
  have hδAm : δA ^ m = 1 := by
    have h := congrArg (AlgEquiv.restrictScalarsHom A) hδm
    rw [map_pow, map_one] at h
    exact h
  have hperiod (x : X) : D^[m] x = x := integralCoefficientFibreDeck_period f φ δA m hδAm x
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hinertia (x : X) (hx : ev x (StageTwo.integralCoeff F (RegularPairChart.ratio u v)) = 0) :
      D^[α] x = x := by
    have hwE : w ^ m = algebraMap A L (f ε) *
        (algebraMap A L (cE (MvPolynomial.X j))) ^ α := by
      rw [hj]
      exact hw
    apply integralCoefficientFibreDeck_branch_inertia f φ N m α hm cE hcE hinj j
      (f ε) (hε.map f.toRingHom) w hwE hgen ζ hζ δA hδw x
    rw [hj]
    exact hx
  have hp (x : X) : ev (D x) (StageTwo.integralCoeff F (RegularPairChart.ratio u v)) =
      ev x (StageTwo.integralCoeff F (RegularPairChart.ratio u v)) := by
    change x.val (δA.mapIntegralClosure (algebraMap A (integralClosure A L) _)) = _
    rw [AlgEquiv.commutes]
    rfl
  obtain ⟨q, t, κ, E, hq, ht, hκ, hκ0, hk, hE⟩ := normalized_binomial_evaluation_homeomorph F
    ev D m α hm (f ε) (RegularPairChart.ratio u v) (hε.map f.toRingHom) hs wN hwN
    δA.toRingEquiv δA.mapIntegralClosure.toRingEquiv (fun _ => rfl) c hc hsσ hwσ
    (φ ε) ζ hε0 hζ hεev hcev heval hcont hproper hsurj horbit hperiod hinertia hp
  exact ⟨E, (fun l => (κ * (ζ ^ (m / Nat.gcd m α)) ^ l.val) ^
    (-Nat.gcdB (m / Nat.gcd m α) (α / Nat.gcd m α))), hk, fun x => (hE x).2.2⟩

end
end AlgebraicGeometry.RamifiedNormalization.StageFour

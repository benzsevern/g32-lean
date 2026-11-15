import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeParameters
import HodgeLean.Adapters.NormalConeB4aGysinLocalModelLength
import HodgeLean.Adapters.NormalConeB4aGysinPolynomialParameters

/-! # Étale target parameters in the source stalk

Étale target coordinates generate the target prime after localization.
Extension to a source localization therefore gives the same fibre ideal.
HC no distance; AV milestone no distance.
-/

noncomputable section
open AlgebraicGeometry HodgeLean.Adapters
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem etale_parameters_extend_to_same_source_ideal
    {A B S : Type} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    [Algebra.Etale A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (r : Ideal S) [r.IsPrime] [r.LiesOver q] :
    p.map (algebraMap A (Localization.AtPrime r)) =
      q.map (algebraMap B (Localization.AtPrime r)) := by
  letI : Algebra (Localization.AtPrime q) (Localization.AtPrime r) :=
    Localization.AtPrime.algebraOfLiesOver q r
  have h := congrArg (fun I : Ideal (Localization.AtPrime q) =>
    I.map (algebraMap (Localization.AtPrime q) (Localization.AtPrime r)))
      (a3b4a_gysin_etale_base_prime_ideal p q)
  simpa only [Ideal.map_map, ← IsScalarTower.algebraMap_eq] using h

theorem etale_zero_parameters_generate_local_maximal
    {d : ℕ} {B : Type} [CommRing B]
    [Algebra (MvPolynomial (Fin d) ℂ) B] [Algebra.Etale (MvPolynomial (Fin d) ℂ) B]
    (q : Ideal B) [q.IsPrime]
    [q.LiesOver (RingHom.ker (MvPolynomial.aeval (R := ℂ) (0 : Fin d → ℂ)))] :
    Ideal.ofList (List.ofFn fun j : Fin d =>
      algebraMap (MvPolynomial (Fin d) ℂ) (Localization.AtPrime q) (MvPolynomial.X j)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  let A := MvPolynomial (Fin d) ℂ
  let p := RingHom.ker (MvPolynomial.aeval (R := ℂ) (0 : Fin d → ℂ))
  letI : p.IsPrime := RingHom.ker_isPrime (MvPolynomial.aeval (R := ℂ) (0 : Fin d → ℂ))
  calc
    _ = (Ideal.ofList (List.ofFn fun j : Fin d => (MvPolynomial.X j : A))).map
        (algebraMap A (Localization.AtPrime q)) := by
      rw [Ideal.map_ofList, List.map_ofFn]
      rfl
    _ = p.map (algebraMap A (Localization.AtPrime q)) :=
      congrArg (Ideal.map (algebraMap A (Localization.AtPrime q)))
        (a3b4a_gysin_zero_parameter_ideal d)
    _ = q.map (algebraMap B (Localization.AtPrime q)) :=
      a3b4a_gysin_etale_base_prime_ideal p q
    _ = _ := Localization.AtPrime.map_eq_maximalIdeal

end AlgebraicGeometry.SingularCycles

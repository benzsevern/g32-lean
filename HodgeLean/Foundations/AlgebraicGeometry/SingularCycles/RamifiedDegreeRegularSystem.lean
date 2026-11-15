import HodgeLean.Adapters.NormalConeB4aGysinBridge2RegularParameters
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeEtaleParameters

/-! # Regular systems of maximal-ideal generators

A list of the dimension's length generating the maximal ideal of a regular
local ring is a regular sequence, with a nonzero residue-field quotient.
HC no distance; AV milestone no distance.
-/

noncomputable section
open IsLocalRing RingTheory.Sequence HodgeLean.Adapters
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem regular_sequence_of_maximal_generators
    (A : Type) [CommRing A] [IsRegularLocalRing A]
    (d : ℕ) (rs : List A) (hdim : ringKrullDim A = d) (hlen : rs.length = d)
    (hgen : Ideal.ofList rs = maximalIdeal A) : IsRegular A rs := by
  have hmem : ∀ r ∈ rs, r ∈ maximalIdeal A := fun r hr => hgen ▸ Ideal.subset_span hr
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
  exact a3b4g_isWeaklyRegular_of_ofList_eq_maximalIdeal d A rs hdim hlen hgen

theorem etale_zero_parameters_are_regular
    {d : ℕ} {B : Type} [CommRing B]
    [Algebra (MvPolynomial (Fin d) ℂ) B] [Algebra.Etale (MvPolynomial (Fin d) ℂ) B]
    (q : Ideal B) [q.IsPrime]
    [q.LiesOver (RingHom.ker (MvPolynomial.aeval (R := ℂ) (0 : Fin d → ℂ)))]
    [IsRegularLocalRing (Localization.AtPrime q)]
    (hdim : ringKrullDim (Localization.AtPrime q) = d) :
    IsRegular (Localization.AtPrime q) (List.ofFn fun j : Fin d =>
      algebraMap (MvPolynomial (Fin d) ℂ) (Localization.AtPrime q) (MvPolynomial.X j)) := by
  exact regular_sequence_of_maximal_generators (Localization.AtPrime q) d _ hdim
    List.length_ofFn (etale_zero_parameters_generate_local_maximal q)

end AlgebraicGeometry.SingularCycles

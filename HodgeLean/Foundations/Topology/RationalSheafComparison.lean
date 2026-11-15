import HodgeLean.Foundations.Topology.RationalSheafComparisonProofs

/-! Rational singular and constant-sheaf comparison interfaces.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Topology.RationalSheafComparison

variable (X : TopCat.{0})
  (hX : ∀ (x : X) (U : Opens X), x ∈ U →
    ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
  [T2Space X] [∀ U : Opens X, ParacompactSpace U]

/-- Rational cochains compute the normalized constant-sheaf resolution.
Source: Bredon, Sheaf Theory, second edition, II.4 and II.6. -/
theorem comparisonComplex_quasiIso : QuasiIso (comparisonComplex X hX) :=
  comparisonComplex_quasiIso_aux X hX

/-- The canonical additive comparison is bijective and has the actual rational coefficient action.
Source: Bredon, Sheaf Theory, second edition, II.4, II.6 and III.1. -/
theorem comparison_linearEquiv (n : ℕ) :
    Function.Bijective (comparison X hX n) ∧
      ∃ e : Cohomology ℚ X n ≃ₗ[ℚ] Sheaf.H (constants X) n,
        ∀ v, e v = comparison X hX n v :=
  comparison_linearEquiv_aux X hX n

omit [T2Space X] [∀ U : Opens X, ParacompactSpace U] in
/-- Multiplication by any rational commutes with the comparison.
Source: Bredon, Sheaf Theory, second edition, II.4; ComplexSheafSingularParts/Scalar. -/
theorem comparison_scalar (n : ℕ) (a : ℚ) (v : Cohomology ℚ X n) :
    comparison X hX n (a • v) =
      Sheaf.H.map (scalar X a) n (comparison X hX n v) :=
  comparison_scalar_aux X hX n a v

/-- The square uses singular pullback and inverse image on Ext, with the constant adjunction isos.
Source: Bredon, Sheaf Theory, second edition, II.4, II.6 and III.1. -/
theorem comparison_naturality (Y : TopCat.{0})
    (hY : ∀ (y : Y) (U : Opens Y), y ∈ U →
      ∃ V : Opens Y, y ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    [T2Space Y] [∀ U : Opens Y, ParacompactSpace U]
    (f : X ⟶ Y) (n : ℕ) (v : Cohomology ℚ Y n) :
    comparison X hX n (cohomologyMap ℚ n f v) =
      sheafPullback f n (comparison Y hY n v) :=
  comparison_naturality_aux X hX Y hY f n v

end HodgeLean.Topology.RationalSheafComparison

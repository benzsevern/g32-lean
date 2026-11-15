import HodgeLean.Foundations.Program.SchoenSegrePowerCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual normalized coordinate in one factor of a finite projective tuple chart. -/
def s2_segrePowerCoord (d n : ℕ) (a : Fin n → Fin (d + 1))
    (i : Fin n) (k : Fin (d + 1)) : Γ(s2_segrePowerChart d n a, ⊤) :=
  (s2_schemeProductπ n _ i).appTop.hom
    ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate (a i) k))

/-- The selected denominator coordinate is the unit section in each actual factor chart. -/
theorem s2_segrePowerCoord_self (d n : ℕ) (a : Fin n → Fin (d + 1)) (i : Fin n) :
    s2_segrePowerCoord d n a i (a i) = 1 := by
  rw [s2_segrePowerCoord, chartCoordinate_self, map_one, map_one]

/-- The actual finite-factor Segre polynomial evaluation on a tuple chart. -/
def s2_segrePowerSections (d n : ℕ) (a : Fin n → Fin (d + 1)) :
    MvPolynomial (Fin n → Fin (d + 1)) (ULift.{0} ℤ) →+* Γ(s2_segrePowerChart d n a, ⊤) :=
  eval₂Hom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
    (fun b => ∏ i, s2_segrePowerCoord d n a i (b i))

/-- Each Segre coordinate evaluates to its actual product of normalized factor coordinates. -/
theorem s2_segrePowerSections_X (d n : ℕ) (a b : Fin n → Fin (d + 1)) :
    s2_segrePowerSections d n a (X b) = ∏ i, s2_segrePowerCoord d n a i (b i) :=
  eval₂Hom_X' _ _ _

/-- The tuple selected for an actual Segre chart evaluates to the unit section. -/
theorem s2_segrePowerSections_X_self (d n : ℕ) (a : Fin n → Fin (d + 1)) :
    s2_segrePowerSections d n a (X a) = 1 := by
  rw [s2_segrePowerSections_X]
  simp only [s2_segrePowerCoord_self, Finset.prod_const_one]

/-- The actual Segre chart evaluation maps the irrelevant ideal onto the unit ideal. -/
theorem s2_segrePowerSections_irrelevant (d n : ℕ) (a : Fin n → Fin (d + 1)) :
    (HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin n → Fin (d + 1)) (ULift.{0} ℤ))).toIdeal.map
        (s2_segrePowerSections d n a) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ zero_lt_one
      (isHomogeneous_X _ a)))
    (by rw [s2_segrePowerSections_X_self]; exact isUnit_one)

/-- The actual finite-factor Segre scheme morphism on an affine tuple chart. -/
def s2_segrePowerChartMap (d n : ℕ) (a : Fin n → Fin (d + 1)) :
    s2_segrePowerChart d n a ⟶
      Proj (homogeneousSubmodule (Fin n → Fin (d + 1)) (ULift.{0} ℤ)) :=
  Proj.fromOfGlobalSections _ (s2_segrePowerSections d n a)
    (s2_segrePowerSections_irrelevant d n a)

end HodgeLean.Foundations.Program

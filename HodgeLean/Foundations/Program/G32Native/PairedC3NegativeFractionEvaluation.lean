import HodgeLean.Foundations.Program.G32Native.PairedC3FractionTransport

/-! # Numerator and denominator of the actual negative-fraction coefficient -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open ProjSpaceCech AlgebraicGeometry.ProjSpace
open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous fraction is determined by its denominator exponents and numerator. -/
theorem paired_c3_fraction_ext {R : Type} [CommRing R] {n : ℕ}
    {D : GradedModule R n} {I : Finset (Fin (n + 1))}
    {p q : GradedModule.Frac D I} (hd : p.denExp = q.denExp) (hn : p.num = q.num) : p = q := by
  cases p
  cases q
  cases hd
  cases hn
  rfl

/-- Multiplying the negative numerator by one coordinate yields a degree-zero
fraction with the original denominator. -/
def pairedC3NegativeRaisedFraction (R : Type) [CommRing R] (n : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1))
    (q : GradedModule.Frac (GradedModule.FD R n (-1)) I) :
    GradedModule.Frac (GradedModule.free R n) I where
  denExp := q.denExp
  hden := q.hden
  num := (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) *
    (show MvPolynomial (Fin (n + 1)) R from q.num)
  hnum := by
    have hp := (GradedModule.free R n).xMul_mem_grade i
      ((∑ j, (q.denExp j : ℤ)) + (-1)) q.num q.hnum
    have hdeg : ((∑ j, (q.denExp j : ℤ)) + (-1)) + 1 = ∑ j, (q.denExp j : ℤ) := by omega
    rw [hdeg] at hp
    exact hp

#print axioms pairedC3NegativeRaisedFraction
/-- The established coefficient equivalence has the literal raised numerator
and the original coordinate denominator on every representative. -/
theorem paired_c3_negative_coefficient_mk (R : Type) [CommRing R] (n : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I)
    (q : GradedModule.Frac (GradedModule.FD R n (-1)) I) :
    pairedC3NegativeFractionCoefficient R n i hi (GradedModule.sec.mk _ I q) =
      unitFreeFractionEquiv R n I ⟨i, hi⟩
        (GradedModule.sec.mk _ I (pairedC3NegativeRaisedFraction R n i q)) := by
  let D := (GradedModule.free R n).shift (-1)
  let φ := GradedModule.coordinateRaiseHom D 1 i
  let q' : GradedModule.Frac (D.shift 1) I :=
    ⟨q.denExp, q.hden, φ.toLinearMap q.num, φ.mem_grade _ _ q.hnum⟩
  have h : D.shift 1 = GradedModule.free R n := by
    dsimp only [D]
    rw [paired_c3_shift_add]
    norm_num
    exact paired_c3_shift_zero _
  change unitFreeFractionEquiv R n I ⟨i, hi⟩
      (pairedC3FractionEquivOfEq h I (GradedModule.sec.mk _ I q')) = _
  refine (congrArg (unitFreeFractionEquiv R n I ⟨i, hi⟩)
    (paired_c3_fraction_eq_mk h I q')).trans ?_
  apply congrArg (fun z => unitFreeFractionEquiv R n I ⟨i, hi⟩ (GradedModule.sec.mk _ I z))
  apply paired_c3_fraction_ext
  · exact (paired_c3_fraction_eq_data h I q').1
  · calc
      (h ▸ q').num = q'.num := eq_of_heq (paired_c3_fraction_eq_data h I q').2
      _ = (pairedC3NegativeRaisedFraction R n i q).num := by
        change ((GradedModule.free R n).xMul i ^ 1) q.num = _
        rw [pow_one]
        rfl

#print axioms paired_c3_fraction_ext
#print axioms paired_c3_negative_coefficient_mk
end HodgeLean.Foundations.Program.G32Native

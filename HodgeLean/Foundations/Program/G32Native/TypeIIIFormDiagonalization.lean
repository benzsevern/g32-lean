import HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData
import HodgeLean.Foundations.Program.G32Native.TypeIIISkewExpansion
import HodgeLean.Adapters.AbelianCMData

noncomputable section
set_option maxHeartbeats 400000
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open Module
namespace HodgeLean.Foundations.Program.G32Native

/-- A skew-Hermitian form on quaternionic homology with its reduced trace
polarization. Coordinates here need not be orthogonal.
Source: G32 v0.18, section 8, line 689 and the preceding paragraph. -/
structure TypeIIIFormData (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
    [IsProjective A.hom] (pol : HQ A 2) where
  b : ℚ
  b_neg : b < 0
  endomorphisms : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A
  coordinates : Dual ℚ (HQ A 1) ≃ₗ[ℚ] (Fin 3 → ℍ[ℚ, -3, 0, b])
  action : ∀ q x i,
    coordinates (((abelianEnd0Action A (endomorphisms q)).unop).dualMap x) i =
      q * coordinates x i
  T : (Fin 3 → ℍ[ℚ, -3, 0, b]) → (Fin 3 → ℍ[ℚ, -3, 0, b]) → ℍ[ℚ, -3, 0, b]
  add_left : ∀ x y z, T (x + y) z = T x z + T y z
  add_right : ∀ x y z, T x (y + z) = T x y + T x z
  smul_left : ∀ (q : ℍ[ℚ, -3, 0, b]) x y, T (q • x) y = q * T x y
  smul_right : ∀ (q : ℍ[ℚ, -3, 0, b]) x y, T x (q • y) = T x y * star q
  skew : ∀ x y, T y x = -star (T x y)
  regular : ∀ x, (∀ y, T x y = 0) → x = 0
  nondegenerate : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol)
  positive : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) nondegenerate
  trace : ∀ x y,
    y (contract (polarizationVec (torusCohomology_cupProductOf A) pol) x) =
      2 * (T (coordinates x) (coordinates y)).re

variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}

/-- Diagonalize the supplied form using its selected orthogonal basis.
Source: G32 v0.18, section 8, lines 688–689 (quaternionic Gram–Schmidt). -/
def TypeIIIFormData.diagonal (F : TypeIIIFormData A pol) : TypeIIISixfoldData A pol := by
  classical
  letI := typeIIIQuaternionDivisionRing F.b F.b_neg
  have hex := typeIII_skew_orthogonal_basis F.b F.b_neg 3 F.T
    F.add_left F.add_right F.smul_left F.smul_right F.skew F.regular
    (by simp [Module.finrank_pi_fintype])
  let eD := Classical.choose hex
  have horth := (Classical.choose_spec hex).1
  have hdiag := (Classical.choose_spec hex).2
  let e := F.coordinates.trans (eD.equivFun.restrictScalars ℚ)
  let t := fun i => F.T (eD i) (eD i)
  have ht (i) : (t i).re = 0 := by
    have h := congrArg QuaternionAlgebra.re (F.skew (eD i) (eD i))
    simp only [QuaternionAlgebra.re_neg, QuaternionAlgebra.re_star, zero_mul, add_zero] at h
    change (t i).re = -(t i).re at h
    linarith
  let l1 := fun i => (t i).imI
  let l2 := fun i => (t i).imJ
  let l3 := fun i => (t i).imK
  have htEntry (i) : (⟨0, l1 i, l2 i, l3 i⟩ : ℍ[ℚ, -3, 0, F.b]) = t i := by
    ext
    · exact (ht i).symm
    · rfl
    · rfl
    · rfl
  refine { b := F.b, b_neg := F.b_neg, endomorphisms := F.endomorphisms
           pullback := abelianEnd0Action A, pullback_integral := ?_
           homology := e, homology_action := ?_
           l1 := l1, l2 := l2, l3 := l3, diagonal_nonzero := ?_
           nondegenerate := F.nondegenerate, positive := F.positive, trace_eq := ?_ }
  · intro f
    simpa only [one_smul] using spec_g4_abelianEnd0Action_tmul A 1 f
  · intro q x i
    have heq : F.coordinates (((abelianEnd0Action A (F.endomorphisms q)).unop).dualMap x) =
        q • F.coordinates x := by
      funext j
      exact F.action q x j
    change eD.equivFun (F.coordinates (((abelianEnd0Action A (F.endomorphisms q)).unop).dualMap x)) i = _
    rw [heq, map_smul]
    rfl
  · intro i hz
    apply hdiag i
    apply (typeIIIQuaternionNorm_eq_zero F.b F.b_neg (t i)).1
    have hz' : -3 * (t i).imI ^ 2 + F.b * (t i).imJ ^ 2 + 3 * F.b * (t i).imK ^ 2 = 0 := hz
    change (t i).re ^ 2 + 3 * (t i).imI ^ 2 - F.b * (t i).imJ ^ 2 -
      3 * F.b * (t i).imK ^ 2 = 0
    rw [ht]
    linarith
  · intro x y
    rw [F.trace]
    have hexp := typeIII_skew_basis_expansion F.T F.add_left F.add_right
      F.smul_left F.smul_right eD horth (F.coordinates x) (F.coordinates y)
    rw [hexp]
    simp_rw [htEntry]
    rfl

/-- The quaternion parameter is retained. -/
theorem TypeIIIFormData.diagonal_b (F : TypeIIIFormData A pol) :
    F.diagonal.b = F.b :=
  rfl

/-- The endomorphism identification is retained. -/
theorem TypeIIIFormData.diagonal_endomorphisms (F : TypeIIIFormData A pol) :
    HEq F.diagonal.endomorphisms F.endomorphisms :=
  HEq.rfl

/-- The supplied form gives a diagonal presentation with the same algebra.
Source: G32 v0.18, section 8, lines 688–689. -/
theorem typeIII_form_diagonalization (F : TypeIIIFormData A pol) :
    ∃ Q : TypeIIISixfoldData A pol,
      Q.b = F.b ∧ HEq Q.endomorphisms F.endomorphisms :=
  ⟨F.diagonal, F.diagonal_b, F.diagonal_endomorphisms⟩

end HodgeLean.Foundations.Program.G32Native
#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_form_diagonalization

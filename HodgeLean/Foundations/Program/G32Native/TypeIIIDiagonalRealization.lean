import HodgeLean.Foundations.Program.G32Native.TypeIIIModelPairing
import HodgeLean.Foundations.Program.G32Native.TypeIIISkewExpansion

noncomputable section
set_option maxHeartbeats 400000
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open Module
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite

/-- The ordinary positive polarized setting supplies the diagonal equivariant
trace presentation, retaining its quaternion algebra and endomorphism map. -/
theorem typeIII_diagonal_trace_realization (b : ℚ) (hb : b < 0)
    (θ : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A) (hdim : dim A.left = 6)
    (hω : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hω) :
    ∃ (e : Dual ℚ (HQ A 1) ≃ₗ[ℚ] (Fin 3 → ℍ[ℚ, -3, 0, b])) (l1 l2 l3 : Fin 3 → ℚ),
      (∀ q x i, e (((abelianEnd0Action A (θ q)).unop).dualMap x) i = q * e x i) ∧
      (∀ i, (-3 * l1 i ^ 2 + b * l2 i ^ 2 + 3 * b * l3 i ^ 2) ≠ 0) ∧
      (∀ x y, y (contract (polarizationVec (torusCohomology_cupProductOf A) pol) x) =
        2 * (∑ i, e x i * (⟨0, l1 i, l2 i, l3 i⟩ : ℍ[ℚ, -3, 0, b]) * star (e y i)).re) := by
  classical
  letI := typeIIIQuaternionDivisionRing b hb
  have hb0 : b ≠ 0 := ne_of_lt hb
  have hP : p1_IsPolarization A pol := (p1_isPolarization_iff_aux A pol).2 ⟨hω, hpos⟩
  obtain ⟨e0, he0⟩ := typeIII_homology_rank_three b hb θ hdim
  let B := typeIIIModelPairing b e0 (polarizationVec (torusCohomology_cupProductOf A) pol)
  have hAlt : B.IsAlt := fun x => typeIIIHomologyPairing_isAlt _ (e0.symm x)
  have hnd : B.Nondegenerate := typeIII_bilin_pullback_nondegenerate _
    (typeIIIHomologyPairing_nondegenerate hω) e0.symm
  have hInv : ∀ (q : ℍ[ℚ, -3, 0, b]) x y, B (q • x) y = B x (star q • y) :=
    typeIII_model_pairing_invariant b hb θ hP e0 he0
  let H := typeIIIQuaternionTraceForm b B
  have hAL := typeIIIQuaternionTraceForm_add_left b B
  have hAR := typeIIIQuaternionTraceForm_add_right b B
  have hSL : ∀ (q : ℍ[ℚ, -3, 0, b]) x y, H (q • x) y = q * H x y :=
    fun q x y => typeIIIQuaternionTraceForm_smul_left b hb0 B x y q
  have hSR : ∀ (q : ℍ[ℚ, -3, 0, b]) x y, H x (q • y) = H x y * star q :=
    fun q x y => typeIIIQuaternionTraceForm_smul_right b hb0 B hInv x y q
  have hSK := typeIIIQuaternionTraceForm_skew b hb0 B hAlt hInv
  have hND := typeIIIQuaternionTraceForm_nondegenerate b hb0 B hnd
  obtain ⟨eD, horth, hdiag⟩ := typeIII_skew_orthogonal_basis b hb 3 H hAL hAR
    hSL hSR hSK hND (by simp [Module.finrank_pi_fintype])
  let e := e0.trans (eD.equivFun.restrictScalars ℚ)
  let t : Fin 3 → ℍ[ℚ, -3, 0, b] := fun i => H (eD i) (eD i)
  have ht (i) : (t i).re = 0 := typeIIIQuaternionTraceForm_diagonal_pure b hb0 B hAlt hInv _
  let l1 : Fin 3 → ℚ := fun i => (t i).imI
  let l2 : Fin 3 → ℚ := fun i => (t i).imJ
  let l3 : Fin 3 → ℚ := fun i => (t i).imK
  have htEntry (i) : (⟨0, l1 i, l2 i, l3 i⟩ : ℍ[ℚ, -3, 0, b]) = t i := by
    ext
    · exact (ht i).symm
    · rfl
    · rfl
    · rfl
  refine ⟨e, l1, l2, l3, ?_, ?_, ?_⟩
  · intro q x i
    have heq : e0 (((abelianEnd0Action A (θ q)).unop).dualMap x) = q • e0 x := by
      funext j
      exact he0 q x j
    change eD.equivFun (e0 (((abelianEnd0Action A (θ q)).unop).dualMap x)) i = _
    rw [heq, map_smul]
    rfl
  · intro i hz
    apply hdiag i
    apply (typeIIIQuaternionNorm_eq_zero b hb (t i)).1
    have hz' : -3 * (t i).imI ^ 2 + b * (t i).imJ ^ 2 + 3 * b * (t i).imK ^ 2 = 0 := hz
    change (t i).re ^ 2 + 3 * (t i).imI ^ 2 - b * (t i).imJ ^ 2 -
      3 * b * (t i).imK ^ 2 = 0
    rw [ht]
    linarith
  · intro x y
    have h := typeIIIQuaternionTraceForm_trace b hb0 B (e0 x) (e0 y) 1
    simp only [one_mul, one_smul] at h
    change 2 * (H (e0 x) (e0 y)).re = B (e0 x) (e0 y) at h
    have hexp := typeIII_skew_basis_expansion H hAL hAR hSL hSR eD horth (e0 x) (e0 y)
    rw [hexp] at h
    simp_rw [htEntry]
    change _ = (e0.symm (e0 y)) (contract
      (polarizationVec (torusCohomology_cupProductOf A) pol) (e0.symm (e0 x))) at h
    simp only [e0.symm_apply_apply] at h
    exact h.symm

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_diagonal_trace_realization

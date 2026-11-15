import HodgeLean.Foundations.Program.G32Native.PELPeriodCircleComparison
import Mathlib.Topology.Algebra.MvPolynomial

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
open scoped TensorProduct Matrix
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The marked weight-one Hodge circle has coefficients in the retained real
complex structure, with the negative-i convention on the holomorphic plane. -/
theorem pel_marked_circle_matrix (R : PELSplitReference)
    (F : PELSplitFamily R) (z : PELSplitComponent R) (c : Circle) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ (F.basis z))
      (Algebra.TensorProduct.basis ℂ (F.basis z))
      (g2_circleAction (latticeHodgePieces (F.fibre z).X)
        (spec_latticeHodgePieces_isInternal (F.fibre z).X) c) =
      ((c : ℂ).re : ℂ) • 1 - ((c : ℂ).im : ℂ) •
        z.val.J.map (algebraMap ℝ ℂ) := by
  let A := (F.fibre z).X
  let bc := Algebra.TensorProduct.basis ℂ (F.basis z)
  let br := Algebra.TensorProduct.basis ℂ R.basis
  let m := (F.mark z).toLinearMap.baseChange ℂ
  let M := z.val.J.map (algebraMap ℝ ℂ)
  let J := Matrix.toLin bc bc M
  have hmatrix : LinearMap.toMatrix br bc m = 1 := by
    dsimp only [br, bc, m]
    rw [LinearMap.toMatrix_baseChange]
    have hm : LinearMap.toMatrix R.basis (F.basis z) (F.mark z).toLinearMap = 1 := by
      ext i j
      simp [LinearMap.toMatrix_apply, PELSplitFamily.basis, Module.Basis.map_repr, Matrix.one_apply, Finsupp.single_apply, eq_comm]
    rw [hm, Matrix.map_one] <;> simp
  have hcoord (v : Fin 12 → ℂ) : m (br.equivFun.symm v) = bc.equivFun.symm v := by
    apply bc.equivFun.injective
    rw [bc.equivFun.apply_symm_apply]
    have hh := LinearMap.toMatrix_mulVec_repr br bc m (br.equivFun.symm v)
    rw [hmatrix] at hh
    change (1 : Matrix (Fin 12) (Fin 12) ℂ) *ᵥ
      (br.equivFun (br.equivFun.symm v)) = bc.equivFun (m (br.equivFun.symm v)) at hh
    rw [Matrix.one_mulVec, br.equivFun.apply_symm_apply] at hh
    exact hh.symm
  have hJcoord (x : ℂ ⊗[ℚ] HQ A 1) :
      bc.equivFun (J x) = Matrix.toLin' M (bc.equivFun x) := by
    have hh := LinearMap.toMatrix_mulVec_repr bc bc J x
    dsimp only [J] at hh
    rw [LinearMap.toMatrix_toLin] at hh
    exact hh.symm
  have hσcoord (x : ℂ ⊗[ℚ] HQ A 1) :
      bc.equivFun (HodgeBlocks.sigmaQ _ x) = star (bc.equivFun x) := by
    induction x using TensorProduct.inductionOn with
    | tmul c v =>
      ext i
      simp [HodgeBlocks.sigmaQ, bc, Module.Basis.equivFun_apply]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy, star_add]
  have hJσ (x : ℂ ⊗[ℚ] HQ A 1) :
      J (HodgeBlocks.sigmaQ _ x) = HodgeBlocks.sigmaQ _ (J x) := by
    apply bc.equivFun.injective
    rw [hJcoord, hσcoord, hσcoord, hJcoord]
    ext i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, star_sum, star_mul, mul_comm, M]
  have h10 (x : ℂ ⊗[ℚ] HQ A 1) (hx : x ∈ complexHolomorphicH1 A) :
      J x = -Complex.I • x := by
    have hx' : x ∈ (pelSplitPlane R z.val).map m := by
      rw [F.plane_eq z]
      exact hx
    obtain ⟨u, hu, rfl⟩ := hx'
    obtain ⟨v, hv, rfl⟩ := hu
    change Matrix.toLin' M v + Complex.I • v = 0 at hv
    change J (m (br.equivFun.symm v)) = -Complex.I • m (br.equivFun.symm v)
    rw [hcoord]
    apply bc.equivFun.injective
    rw [hJcoord, bc.equivFun.apply_symm_apply, map_smul, bc.equivFun.apply_symm_apply]
    simpa only [neg_smul] using (add_eq_zero_iff_eq_neg.mp hv)
  have h01 (x : ℂ ⊗[ℚ] HQ A 1) (hx : x ∈ complexAntiholomorphicH1 A) :
      J x = Complex.I • x := by
    rw [← spec_complexH1_conjugation_exchanges A] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [hJσ, h10 u hu, map_smulₛₗ]
    have hi : (starRingEnd ℂ) (-Complex.I) = Complex.I := by
      change star (-Complex.I) = Complex.I
      rw [star_neg, Complex.star_def, Complex.conj_I, neg_neg]
    rw [hi]
  have heq : g2_circleAction (latticeHodgePieces A)
      (spec_latticeHodgePieces_isInternal A) c =
      ((c : ℂ).re : ℂ) • LinearMap.id - ((c : ℂ).im : ℂ) • J := by
    apply linearMap_ext_of_isInternal (spec_latticeHodgePieces_isInternal A)
    intro pq x hx
    by_cases hp : pq = (1, 0)
    · subst pq
      rw [g2_circleAction_apply_of_mem _ _ c hx]
      have hh := h10 x (by simpa only [latticeHodgePieces, ite_true] using hx)
      simp only [sub_zero, zpow_one, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, hh, smul_smul]
      rw [← sub_smul]
      congr 1
      apply Complex.ext <;> simp
    · by_cases hq : pq = (0, 1)
      · subst pq
        rw [g2_circleAction_apply_of_mem _ _ c hx]
        have hh := h01 x (by simpa [latticeHodgePieces] using hx)
        simp only [show (0 : ℤ) - 1 = -1 by rfl, zpow_neg_one,
          LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hh, smul_smul]
        rw [← sub_smul]
        congr 1
        rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
        apply Complex.ext <;> simp
      · have hx0 : x = 0 := by
          simpa only [latticeHodgePieces, if_neg hp, if_neg hq, Submodule.mem_bot] using hx
        subst x
        simp only [map_zero]
  change LinearMap.toMatrix bc bc _ = _
  rw [heq, map_sub, map_smul, map_smul, LinearMap.toMatrix_id]
  simp only [J, LinearMap.toMatrix_toLin]
  rfl

#print axioms pel_marked_circle_matrix
end HodgeLean.Foundations.Program.GeneralTypeIII

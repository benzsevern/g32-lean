import HodgeLean.Blocks.Weil.RationalKernel
import HodgeLean.Blocks.Weil.WeilClasses

/-! # Weil's theorem, restated with `IsHodgeClass` -/

open scoped TensorProduct

noncomputable section
namespace HodgeBlocks

set_option maxHeartbeats 4000000

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

namespace WeilAction

variable {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)

def tensorPowerToExteriorPowerComplex (n : ℕ) :
    TensorPower ℂ n (TensorProduct ℚ ℂ V) →ₗ[ℂ] (⋀[ℂ]^n (TensorProduct ℚ ℂ V)) :=
  PiTensorProduct.lift (exteriorPower.ιMulti ℂ n (M := TensorProduct ℚ ℂ V)).toMultilinearMap

@[simp] theorem tensorPowerToExteriorPowerComplex_tprod (n : ℕ)
    (v : Fin n → TensorProduct ℚ ℂ V) :
    tensorPowerToExteriorPowerComplex (V := V) n (PiTensorProduct.tprod ℂ v) =
      exteriorPower.ιMulti ℂ n v :=
  PiTensorProduct.lift.tprod v

private theorem exteriorPowerBaseChangeEquiv_tmul' (n : ℕ) (c : ℂ)
    (w : ⋀[ℚ]^n V) :
    exteriorPowerBaseChangeEquiv (V := V) n (c ⊗ₜ[ℚ] w) =
      c • complexifyWedge n w := by
  rw [TensorProduct.tmul_eq_smul_one_tmul]
  rw [map_smul, exteriorPowerBaseChangeEquiv_tmul]

private theorem tensorPowerToExteriorPowerComplex_tmul_tprod' (n : ℕ) (c : ℂ)
    (v : Fin n → V) :
    tensorPowerToExteriorPowerComplex (V := V) n
        (c • PiTensorProduct.tprod ℂ (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i)) =
      c • exteriorPower.ιMulti ℂ n (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i) := by
  rw [map_smul, tensorPowerToExteriorPowerComplex_tprod]

private theorem exteriorPowerBaseChangeEquiv_rational_smul (n : ℕ) (r : ℚ)
    (x : ℂ ⊗[ℚ] (⋀[ℚ]^n V)) :
    exteriorPowerBaseChangeEquiv (V := V) n (r • x) =
      (r : ℂ) • exteriorPowerBaseChangeEquiv (V := V) n x := by
  change exteriorPowerBaseChangeEquiv (V := V) n ((r : ℂ) • x) = _
  rw [map_smul]

/-- The complexified rational wedge quotient agrees with the complex wedge quotient after
transporting tensor powers through scalar extension. -/
theorem exteriorPowerBaseChangeEquiv_baseChange_tensorPowerToExteriorPower (n : ℕ)
    (x : TensorProduct ℚ ℂ (TensorPower ℚ n V)) :
    exteriorPowerBaseChangeEquiv (V := V) n
        ((tensorPowerToExteriorPower V n).baseChange ℂ x) =
      tensorPowerToExteriorPowerComplex (V := V) n (tensorPowerBaseChange V n x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c z =>
      induction z using PiTensorProduct.induction_on generalizing c with
      | smul_tprod r v =>
          rw [LinearMap.baseChange_tmul]
          have hleft :
              tensorPowerToExteriorPower V n (r • PiTensorProduct.tprod ℚ v) =
                r • exteriorPower.ιMulti ℚ n v := by
            rw [map_smul, tensorPowerToExteriorPower_tprod]
          rw [hleft]
          rw [TensorProduct.tmul_smul]
          have hmove :
              c ⊗ₜ[ℚ] (r • PiTensorProduct.tprod ℚ v) =
                ((r : ℂ) • c) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v := by
            rw [TensorProduct.tmul_smul (R := ℚ) (R' := ℚ)
              (M := ℂ) (N := TensorPower ℚ n V)]
            simp only [Algebra.smul_def]
            change r • c ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v =
              ((r : ℂ) * c) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v
            congr 1
          rw [hmove]
          rw [tensorPowerBaseChange_tmul_tprod]
          rw [PiTensorProduct.tprodCoeff_eq_smul_tprod]
          rw [tensorPowerToExteriorPowerComplex_tmul_tprod']
          change exteriorPowerBaseChangeEquiv (V := V) n
              (r • (c ⊗ₜ[ℚ] exteriorPower.ιMulti ℚ n v)) = _
          rw [exteriorPowerBaseChangeEquiv_rational_smul]
          rw [exteriorPowerBaseChangeEquiv_tmul' n c
            (exteriorPower.ιMulti ℚ n v)]
          rw [complexifyWedge_ιMulti]
          rw [smul_smul]
          simp [Algebra.smul_def]
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A decomposable complex wedge whose factors lie in prescribed Hodge pieces belongs to the
transported exterior-power Hodge piece. -/
theorem exteriorPower_ιMulti_mem_exteriorPowerH_map
    (M : QHodgeStructure 1 V) (n : ℕ) (q : ℤ × ℤ)
    (d : Fin n → ℤ × ℤ) (v : Fin n → TensorProduct ℚ ℂ V)
    (hd : totalBidegree n d = q) (hv : ∀ i, v i ∈ M.H (d i)) :
    exteriorPower.ιMulti ℂ n v ∈
      (M.exteriorPowerH (V := V) n q).map
        (exteriorPowerBaseChangeEquiv (V := V) n).toLinearMap := by
  classical
  let K := LinearMap.ker (tensorPowerAltC V n)
  let e := QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (V := V) n
  have hfine :
      PiTensorProduct.tprod ℂ v ∈ M.tensorFinePiece (V := V) n d := by
    refine ⟨PiTensorProduct.tprod ℂ
      (fun i => (⟨v i, hv i⟩ : M.H (d i))), ?_⟩
    rw [PiTensorProduct.map_tprod]
    rfl
  have hsum :
      PiTensorProduct.tprod ℂ v ∈
        ⨆ d' ∈ (totalBidegree n) ⁻¹' {q}, M.tensorFinePiece (V := V) n d' := by
    exact Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hd hfine)
  let y := (tensorPowerBaseChange V n).symm (PiTensorProduct.tprod ℂ v)
  have hy : y ∈ (M.tensorPowerFlat (V := V) n).H q := by
    dsimp [y]
    change (tensorPowerBaseChange V n).symm (PiTensorProduct.tprod ℂ v) ∈
      (⨆ d' ∈ (totalBidegree n) ⁻¹' {q}, M.tensorFinePiece (V := V) n d').map
        (tensorPowerBaseChange V n).symm.toLinearMap
    rw [Submodule.mem_map_equiv]
    simp only [LinearEquiv.symm_symm]
    simpa only [LinearEquiv.apply_symm_apply] using hsum
  have hquot : K.mkQ y ∈
      ((M.tensorPowerFlat (V := V) n).H q).map K.mkQ :=
    Submodule.mem_map_of_mem hy
  have himage :
      exteriorPowerBaseChangeEquiv (V := V) n
          ((tensorPowerToExteriorPower V n).baseChange ℂ y) =
        exteriorPower.ιMulti ℂ n v := by
    rw [exteriorPowerBaseChangeEquiv_baseChange_tensorPowerToExteriorPower]
    change tensorPowerToExteriorPowerComplex (V := V) n
        (tensorPowerBaseChange V n y) = _
    dsimp [y]
    rw [LinearEquiv.apply_symm_apply]
    exact tensorPowerToExteriorPowerComplex_tprod (V := V) n v
  rw [QHodgeStructure.exteriorPowerH]
  rw [← himage]
  refine ⟨e (K.mkQ y), ?_, ?_⟩
  · exact Submodule.mem_map_of_mem hquot
  · exact congrArg (exteriorPowerBaseChangeEquiv (V := V) n)
      (QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC_mk (V := V) n y)


/-- The `(k,k)` wedge-type subspace is contained in the corresponding exterior-power Hodge piece. -/
theorem wedgeType_le_exteriorPowerH_map (M : QHodgeStructure 1 V) (k : ℕ)
    (P Q : Submodule ℂ (ℂ ⊗[ℚ] V)) (hP : P ≤ M.H (1, 0)) (hQ : Q ≤ M.H (0, 1)) :
    wedgeType P Q k k ≤
      (M.exteriorPowerH (V := V) (k + k) (k, k)).map
        (WeilAction.exteriorPowerBaseChangeEquiv (V := V) (k + k)).toLinearMap := by
  rw [wedgeType]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨p, hp, q, hq, rfl⟩
  let d : Fin (k + k) → ℤ × ℤ :=
    Fin.append (fun _ : Fin k => ((1 : ℤ), (0 : ℤ)))
      (fun _ : Fin k => ((0 : ℤ), (1 : ℤ)))
  have hd : totalBidegree (k + k) d = ((k : ℤ), (k : ℤ)) := by
    apply Prod.ext <;>
      simp [totalBidegree, d, Fin.sum_univ_add, Fin.append, Fin.addCases, Fin.cast]
  apply exteriorPower_ιMulti_mem_exteriorPowerH_map M (k + k) (k, k) d
    (Fin.append p q) hd
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [d, Fin.append, Fin.addCases, Fin.cast] using hP (hp j)
  · intro j
    simpa [d, Fin.append, Fin.addCases, Fin.cast] using hQ (hq j)

/-- Every rational Weil class is a Hodge class in the induced exterior-power structure. -/
theorem isHodgeClass_of_mem_weilClasses
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType)
    {w : ⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V}
    (hw : w ∈ A.weilClasses hH hWeil) :
    IsHodgeClass (p := (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) : ℤ))
      (weightCast (V := ⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
        Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V) (by omega)
        (M.exteriorPower (V := V)
          (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
            Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))))) w := by
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  have hwedge := A.weilClasses_mem_wedgeType hH hWeil hw
  have hVs := wedgeType_le_exteriorPowerH_map M k
      (A.Vs ⊓ M.H (1, 0)) (A.Vs ⊓ M.H (0, 1))
      (fun x hx => hx.2) (fun x hx => hx.2)
  have hVsbar := wedgeType_le_exteriorPowerH_map M k
      (A.Vsbar ⊓ M.H (1, 0)) (A.Vsbar ⊓ M.H (0, 1))
      (fun x hx => hx.2) (fun x hx => hx.2)
  have hmap : complexifyWedge (k + k) w ∈
      (M.exteriorPowerH (V := V) (k + k) (k, k)).map
        (exteriorPowerBaseChangeEquiv (V := V) (k + k)).toLinearMap := by
    exact (sup_le hVs hVsbar) hwedge
  change complexify (⋀[ℚ]^(k + k) V) w ∈
    (weightCast (V := ⋀[ℚ]^(k + k) V) (by omega)
      (M.exteriorPower (V := V) (k + k))).H (k, k)
  rw [weightCast_H]
  change complexify (⋀[ℚ]^(k + k) V) w ∈
    (M.exteriorPowerH (V := V) (k + k) (k, k))
  have hmap' :
      exteriorPowerBaseChangeEquiv (V := V) (k + k)
          ((1 : ℂ) ⊗ₜ[ℚ] w) ∈
        (M.exteriorPowerH (V := V) (k + k) (k, k)).map
          (exteriorPowerBaseChangeEquiv (V := V) (k + k)).toLinearMap := by
    rw [exteriorPowerBaseChangeEquiv_tmul]
    exact hmap
  rw [Submodule.mem_map_equiv] at hmap'
  simpa only [LinearEquiv.symm_apply_apply, complexify_apply] using hmap'

end WeilAction
end HodgeBlocks

#print axioms HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_baseChange_tensorPowerToExteriorPower
#print axioms HodgeBlocks.WeilAction.exteriorPower_ιMulti_mem_exteriorPowerH_map
#print axioms HodgeBlocks.WeilAction.wedgeType_le_exteriorPowerH_map
#print axioms HodgeBlocks.WeilAction.isHodgeClass_of_mem_weilClasses

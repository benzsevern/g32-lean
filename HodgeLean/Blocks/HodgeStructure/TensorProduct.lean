import HodgeLean.Blocks.HodgeStructure.DirectSum
import HodgeLean.Blocks.Algebra.TensorInternal

/-! # Tensor products of pure rational Hodge structures -/

open scoped TensorProduct
noncomputable section
namespace HodgeBlocks

variable {V W : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]

/-- Scalar extension commutes with tensor products. -/
def tensorBaseChange :
    (ℂ ⊗[ℚ] (V ⊗[ℚ] W)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] V) ⊗[ℂ] (ℂ ⊗[ℚ] W) :=
  TensorProduct.AlgebraTensorModule.congr
      (TensorProduct.lid ℂ ℂ).symm (LinearEquiv.refl ℚ (V ⊗[ℚ] W)) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
      ℚ ℂ ℚ ℂ ℂ ℂ V W

@[simp] theorem tensorBaseChange_tmul (c : ℂ) (v : V) (w : W) :
    tensorBaseChange (V := V) (W := W) (c ⊗ₜ[ℚ] (v ⊗ₜ[ℚ] w)) =
      ((1 : ℂ) ⊗ₜ[ℚ] v) ⊗ₜ[ℂ] (c ⊗ₜ[ℚ] w) := by
  simp [tensorBaseChange]

/-- The tensor product of two Hodge summands, before the convolution grading is
formed by adding their first indices. -/
def tensorPairPiece {n m : ℤ} [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W) (p : ℤ × ℤ) :
    Submodule ℂ ((ℂ ⊗[ℚ] V) ⊗[ℂ] (ℂ ⊗[ℚ] W)) :=
  LinearMap.range (TensorProduct.mapIncl
    (M.H (p.1, n - p.1)) (N.H (p.2, m - p.2)))

theorem tmul_mem_tensorPairPiece {n m : ℤ} [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W) (p₁ p₂ : ℤ)
    {x : ℂ ⊗[ℚ] V} (hx : x ∈ M.H (p₁, n - p₁))
    {y : ℂ ⊗[ℚ] W} (hy : y ∈ N.H (p₂, m - p₂)) :
    x ⊗ₜ[ℂ] y ∈ tensorPairPiece M N (p₁, p₂) := by
  exact ⟨⟨x, hx⟩ ⊗ₜ[ℂ] ⟨y, hy⟩, rfl⟩

/-- The tensor product of arbitrary Hodge summands, before their two bidegrees are added. -/
def fullTensorPairPiece {n m : ℤ} [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W)
    (a : (ℤ × ℤ) × (ℤ × ℤ)) :
    Submodule ℂ ((ℂ ⊗[ℚ] V) ⊗[ℂ] (ℂ ⊗[ℚ] W)) :=
  LinearMap.range (TensorProduct.mapIncl (M.H a.1) (N.H a.2))

/-- Add the two bidegrees indexing a pair of Hodge summands. -/
def addBidegrees (a : (ℤ × ℤ) × (ℤ × ℤ)) : ℤ × ℤ :=
  (a.1.1 + a.2.1, a.1.2 + a.2.2)

/-- The convolution piece of bidegree `pq` in the tensor product decomposition. -/
def tensorConvolutionPiece {n m : ℤ} [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W) (pq : ℤ × ℤ) :
    Submodule ℂ ((ℂ ⊗[ℚ] V) ⊗[ℂ] (ℂ ⊗[ℚ] W)) :=
  ⨆ a ∈ addBidegrees ⁻¹' {pq}, fullTensorPairPiece M N a

theorem tensorConvolutionPiece_isInternal {n m : ℤ}
    [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W) :
    DirectSum.IsInternal (tensorConvolutionPiece M N) := by
  exact (M.isInternal.tensor N.isInternal).regroupFibers addBidegrees

theorem tensorConvolutionPiece_supported {n m : ℤ}
    [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W) (pq : ℤ × ℤ)
    (h : pq.1 + pq.2 ≠ n + m) : tensorConvolutionPiece M N pq = ⊥ := by
  apply iSup_eq_bot.2
  intro a
  apply iSup_eq_bot.2
  intro ha
  have ha' : addBidegrees a = pq := by simpa using ha
  by_cases hM : a.1.1 + a.1.2 = n
  · have hN : a.2.1 + a.2.2 ≠ m := by
      intro hN
      apply h
      have hsum := congrArg (fun z : ℤ × ℤ => z.1 + z.2) ha'
      dsimp [addBidegrees] at hsum
      omega
    unfold fullTensorPairPiece
    rw [N.supported a.2 hN]
    exact LinearMap.range_eq_bot.2 (by
      ext z x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp)
  · unfold fullTensorPairPiece
    rw [M.supported a.1 hM]
    exact LinearMap.range_eq_bot.2 (by
      ext z x
      have hz : z = 0 := Subsingleton.elim _ _
      subst z
      simp)

/-- Under scalar extension, rational conjugation on a tensor product is the
tensor product of rational conjugation on its two factors. -/
theorem tensorBaseChange_sigmaQR (x : ℂ ⊗[ℚ] (V ⊗[ℚ] W)) :
    tensorBaseChange (V := V) (W := W) (sigmaQR (V ⊗[ℚ] W) x) =
      TensorProduct.map (sigmaQ V) (sigmaQ W)
        (tensorBaseChange (V := V) (W := W) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c z =>
      induction z using TensorProduct.induction_on generalizing c with
      | zero => simp
      | tmul v w =>
          change ((1 : ℂ) ⊗ₜ[ℚ] v) ⊗ₜ[ℂ] ((starRingEnd ℂ) c ⊗ₜ[ℚ] w) =
            sigmaQR V (1 ⊗ₜ[ℚ] v) ⊗ₜ[ℂ] sigmaQR W (c ⊗ₜ[ℚ] w)
          simp
      | add z₁ z₂ hz₁ hz₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add, hz₁, hz₂,
            map_add, map_add]
  | add x y hx hy => simp only [map_add, hx, hy]

def swapTensorBidegrees (a : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((a.1.2, a.1.1), (a.2.2, a.2.1))

@[simp] theorem swapTensorBidegrees_involutive (a : (ℤ × ℤ) × (ℤ × ℤ)) :
    swapTensorBidegrees (swapTensorBidegrees a) = a := by
  rcases a with ⟨⟨p, q⟩, ⟨r, s⟩⟩
  rfl

theorem tensorSigma_involutive
    (x : (ℂ ⊗[ℚ] V) ⊗[ℂ] (ℂ ⊗[ℚ] W)) :
    TensorProduct.map (sigmaQ V) (sigmaQ W)
      (TensorProduct.map (sigmaQ V) (sigmaQ W) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.map_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem tensorSigma_mem_fullTensorPairPiece {n m : ℤ}
    [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W)
    (a : (ℤ × ℤ) × (ℤ × ℤ))
    {x : (ℂ ⊗[ℚ] V) ⊗[ℂ] (ℂ ⊗[ℚ] W)}
    (hx : x ∈ fullTensorPairPiece M N a) :
    TensorProduct.map (sigmaQ V) (sigmaQ W) x ∈
      fullTensorPairPiece M N (swapTensorBidegrees a) := by
  rcases hx with ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => simp [fullTensorPairPiece]
  | tmul u v =>
      refine ⟨⟨sigmaQ V u, ?_⟩ ⊗ₜ[ℂ] ⟨sigmaQ W v, ?_⟩, ?_⟩
      · change sigmaQ V u ∈ M.H (a.1.2, a.1.1)
        rw [← M.conj_symm a.1.1 a.1.2]
        exact Submodule.mem_map_of_mem u.property
      · change sigmaQ W v ∈ N.H (a.2.2, a.2.1)
        rw [← N.conj_symm a.2.1 a.2.2]
        exact Submodule.mem_map_of_mem v.property
      · rfl
  | add x y hx hy => simpa [map_add] using Submodule.add_mem _ hx hy

theorem map_tensorSigma_fullTensorPairPiece {n m : ℤ}
    [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W)
    (a : (ℤ × ℤ) × (ℤ × ℤ)) :
    (fullTensorPairPiece M N a).map (TensorProduct.map (sigmaQ V) (sigmaQ W)) =
      fullTensorPairPiece M N (swapTensorBidegrees a) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact tensorSigma_mem_fullTensorPairPiece M N a hx
  · intro x hx
    refine ⟨TensorProduct.map (sigmaQ V) (sigmaQ W) x, ?_, ?_⟩
    · simpa using tensorSigma_mem_fullTensorPairPiece M N (swapTensorBidegrees a) hx
    · exact tensorSigma_involutive x

theorem map_tensorSigma_tensorConvolutionPiece {n m : ℤ}
    [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W) (p q : ℤ) :
    (tensorConvolutionPiece M N (p, q)).map
        (TensorProduct.map (sigmaQ V) (sigmaQ W)) =
      tensorConvolutionPiece M N (q, p) := by
  simp only [tensorConvolutionPiece, Submodule.map_iSup]
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun ha => ?_
    rw [map_tensorSigma_fullTensorPairPiece]
    refine le_iSup_of_le (swapTensorBidegrees a) (le_iSup_of_le ?_ le_rfl)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ⊢
    rcases a with ⟨⟨i, j⟩, ⟨k, l⟩⟩
    simp only [addBidegrees, swapTensorBidegrees, Prod.fst, Prod.snd] at ha ⊢
    rcases Prod.mk.inj ha with ⟨h₁, h₂⟩
    exact Prod.ext h₂ h₁
  · refine iSup_le fun a => iSup_le fun ha => ?_
    refine le_iSup_of_le (swapTensorBidegrees a) (le_iSup_of_le ?_ ?_)
    · simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ⊢
      rcases a with ⟨⟨i, j⟩, ⟨k, l⟩⟩
      simp only [addBidegrees, swapTensorBidegrees, Prod.fst, Prod.snd] at ha ⊢
      rcases Prod.mk.inj ha with ⟨h₁, h₂⟩
      exact Prod.ext h₂ h₁
    · simpa using (map_tensorSigma_fullTensorPairPiece M N
        (swapTensorBidegrees a)).symm.le

theorem sigma_tensorBaseChange_symm
    (y : (ℂ ⊗[ℚ] V) ⊗[ℂ] (ℂ ⊗[ℚ] W)) :
    sigmaQ (V ⊗[ℚ] W) ((tensorBaseChange (V := V) (W := W)).symm y) =
      (tensorBaseChange (V := V) (W := W)).symm
        (TensorProduct.map (sigmaQ V) (sigmaQ W) y) := by
  apply (tensorBaseChange (V := V) (W := W)).injective
  change tensorBaseChange (sigmaQR (V ⊗[ℚ] W) _) = _
  rw [tensorBaseChange_sigmaQR, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

theorem map_sigma_tensorBaseChange_symm
    (P : Submodule ℂ ((ℂ ⊗[ℚ] V) ⊗[ℂ] (ℂ ⊗[ℚ] W))) :
    (P.map (tensorBaseChange (V := V) (W := W)).symm.toLinearMap).map
        (sigmaQ (V ⊗[ℚ] W)) =
      (P.map (TensorProduct.map (sigmaQ V) (sigmaQ W))).map
        (tensorBaseChange (V := V) (W := W)).symm.toLinearMap := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨TensorProduct.map (sigmaQ V) (sigmaQ W) y,
      Submodule.mem_map_of_mem hy, (sigma_tensorBaseChange_symm y).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨(tensorBaseChange (V := V) (W := W)).symm y,
      ⟨y, hy, rfl⟩, sigma_tensorBaseChange_symm y⟩

/-- Tensor product of pure rational Hodge structures, with convolution Hodge decomposition. -/
def QHodgeStructure.tensor {n m : ℤ} [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W) :
    QHodgeStructure (n + m) (V ⊗[ℚ] W) where
  H pq := (tensorConvolutionPiece M N pq).map
    (tensorBaseChange (V := V) (W := W)).symm.toLinearMap
  supported pq h := by
    rw [tensorConvolutionPiece_supported M N pq h, Submodule.map_bot]
  isInternal := (tensorConvolutionPiece_isInternal M N).mapEquiv
    (tensorBaseChange (V := V) (W := W)).symm
  conj_symm p q := by
    rw [map_sigma_tensorBaseChange_symm,
      map_tensorSigma_tensorConvolutionPiece M N p q]

#print axioms QHodgeStructure.tensor

/-- The tensor product with its weight normalized to `2 * (p + q)`, for use with
`IsHodgeClass`, whose type records weights in that syntactic form. -/
def QHodgeStructure.tensorHodge {p q : ℤ} [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure (2 * p) V) (N : QHodgeStructure (2 * q) W) :
    QHodgeStructure (2 * (p + q)) (V ⊗[ℚ] W) where
  H ij := (tensorConvolutionPiece M N ij).map
    (tensorBaseChange (V := V) (W := W)).symm.toLinearMap
  supported ij h := by
    rw [tensorConvolutionPiece_supported M N ij (by omega), Submodule.map_bot]
  isInternal := (tensorConvolutionPiece_isInternal M N).mapEquiv
    (tensorBaseChange (V := V) (W := W)).symm
  conj_symm i j := by
    rw [map_sigma_tensorBaseChange_symm,
      map_tensorSigma_tensorConvolutionPiece M N i j]

#print axioms QHodgeStructure.tensorHodge

theorem QHodgeStructure.tensorHodge_H {p q : ℤ}
    [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure (2 * p) V) (N : QHodgeStructure (2 * q) W)
    (ij : ℤ × ℤ) :
    (QHodgeStructure.tensorHodge M N).H ij =
      (tensorConvolutionPiece M N ij).map
        (tensorBaseChange (V := V) (W := W)).symm.toLinearMap := by
  simp [QHodgeStructure.tensorHodge, QHodgeStructure.tensor]

#print axioms QHodgeStructure.tensorHodge_H

/-- The concrete tensor piece generated by products of vectors in two specified Hodge pieces.
`Submodule.span` (`Mathlib/LinearAlgebra/Span/Basic.lean`) is used because no assertion of a
full tensor-product decomposition is needed for the Hodge-class multiplication theorem. -/
def tensorPiece {n m : ℤ} [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W) (a b : ℤ × ℤ) :
    Submodule ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] W)) :=
  Submodule.span ℂ {z | ∃ v : V, (1 : ℂ) ⊗ₜ[ℚ] v ∈ M.H a ∧
    ∃ w : W, (1 : ℂ) ⊗ₜ[ℚ] w ∈ N.H b ∧ (1 : ℂ) ⊗ₜ[ℚ] (v ⊗ₜ[ℚ] w) = z}

theorem tmul_mem_tensorPiece {n m : ℤ} [Module.Finite ℚ V] [Module.Finite ℚ W]
    (M : QHodgeStructure n V) (N : QHodgeStructure m W) (a b : ℤ × ℤ)
    {v : V} (hv : (1 : ℂ) ⊗ₜ[ℚ] v ∈ M.H a)
    {w : W} (hw : (1 : ℂ) ⊗ₜ[ℚ] w ∈ N.H b) :
    (1 : ℂ) ⊗ₜ[ℚ] (v ⊗ₜ[ℚ] w) ∈ tensorPiece M N a b :=
  Submodule.subset_span ⟨v, hv, w, hw, rfl⟩

#print axioms fullTensorPairPiece
#print axioms addBidegrees
#print axioms tensorConvolutionPiece
#print axioms tensorConvolutionPiece_isInternal
#print axioms tensorConvolutionPiece_supported
#print axioms swapTensorBidegrees
#print axioms swapTensorBidegrees_involutive
#print axioms tensorSigma_involutive
#print axioms tensorSigma_mem_fullTensorPairPiece
#print axioms map_tensorSigma_fullTensorPairPiece
#print axioms map_tensorSigma_tensorConvolutionPiece
#print axioms sigma_tensorBaseChange_symm
#print axioms map_sigma_tensorBaseChange_symm

end HodgeBlocks

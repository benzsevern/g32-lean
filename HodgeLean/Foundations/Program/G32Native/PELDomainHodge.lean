import HodgeLean.Foundations.Program.G32Native.PELSplitDomain
import HodgeLean.Foundations.HodgeGroupAlgebraic

noncomputable section
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The complexified period operator in the reference Betti space. -/
def pelDomainOperator (R : PELSplitReference) (z : PELSplitDomain R) :
    Module.End ℂ (ℂ ⊗[ℚ] HQ R.B.X 1) :=
  Matrix.toLin (Algebra.TensorProduct.basis ℂ R.basis)
    (Algebra.TensorProduct.basis ℂ R.basis) (z.J.map (algebraMap ℝ ℂ))

theorem pelDomainOperator_square (R : PELSplitReference) (z : PELSplitDomain R) :
    pelDomainOperator R z * pelDomainOperator R z = -1 := by
  apply (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ R.basis)
    (Algebra.TensorProduct.basis ℂ R.basis)).injective
  simp only [LinearMap.toMatrix_mul, pelDomainOperator, LinearMap.toMatrix_toLin,
    map_neg, LinearMap.toMatrix_one]
  rw [← Matrix.map_mul, z.square, Matrix.map_neg, Matrix.map_one] <;> simp

theorem pelDomainOperator_conj (R : PELSplitReference) (z : PELSplitDomain R)
    (x : ℂ ⊗[ℚ] HQ R.B.X 1) :
    pelDomainOperator R z (HodgeBlocks.sigmaQ _ x) =
      HodgeBlocks.sigmaQ _ (pelDomainOperator R z x) := by
  let b := Algebra.TensorProduct.basis ℂ R.basis
  have hc (x : ℂ ⊗[ℚ] HQ R.B.X 1) :
      b.equivFun (HodgeBlocks.sigmaQ _ x) = star (b.equivFun x) := by
    induction x using TensorProduct.inductionOn with
    | tmul c v => ext i; simp [HodgeBlocks.sigmaQ, b, Module.Basis.equivFun_apply]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, star_add]
  have hj (x : ℂ ⊗[ℚ] HQ R.B.X 1) :
      b.equivFun (pelDomainOperator R z x) =
        Matrix.toLin' (z.J.map (algebraMap ℝ ℂ)) (b.equivFun x) := by
    have h := LinearMap.toMatrix_mulVec_repr b b (pelDomainOperator R z) x
    dsimp only [pelDomainOperator, b] at h
    rw [LinearMap.toMatrix_toLin] at h
    exact h.symm
  apply b.equivFun.injective
  rw [hj, hc, hc, hj]
  ext i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, star_sum, star_mul, mul_comm]

/-- The two eigenspaces of a complex structure are complementary. -/
theorem pel_isCompl_eigenspaces {V : Type*} [AddCommGroup V] [Module ℂ V]
    (J : Module.End ℂ V) (hJ : J * J = -1) :
    IsCompl (Module.End.eigenspace J (-Complex.I)) (Module.End.eigenspace J Complex.I) := by
  have hj (x : V) : J (J x) = -x := by
    have h := LinearMap.congr_fun hJ x
    simpa using h
  constructor
  · rw [disjoint_iff]
    exact ((Module.End.eigenspaces_iSupIndep J).pairwiseDisjoint
      (show -Complex.I ≠ Complex.I by
        intro h
        have : (2 : ℂ) * Complex.I = 0 := by linear_combination -h
        simp [Complex.I_ne_zero] at this)).eq_bot
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.mpr ⟨(1 / 2 : ℂ) • (x + Complex.I • J x), ?_,
      (1 / 2 : ℂ) • (x - Complex.I • J x), ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      simp only [map_smul, map_add, hj, smul_add, smul_neg, smul_smul]
      rw [show -Complex.I * (1 / 2 * Complex.I) = 1 / 2 by
        ring_nf; rw [Complex.I_sq]; ring]
      module
    · rw [Module.End.mem_eigenspace_iff]
      simp only [map_smul, map_sub, hj, smul_sub, smul_neg, smul_smul]
      rw [show Complex.I * (1 / 2 * Complex.I) = -(1 / 2) by
        ring_nf; rw [Complex.I_sq]; ring]
      module
    · module

/-- The effective weight-one grading of a retained period point.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.1–1.3. -/
def pelDomainPieces (R : PELSplitReference) (z : PELSplitDomain R) :
    ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] HQ R.B.X 1) :=
  fun pq => if pq = (1, 0) then Module.End.eigenspace (pelDomainOperator R z) (-Complex.I)
    else if pq = (0, 1) then Module.End.eigenspace (pelDomainOperator R z) Complex.I else ⊥

theorem pelDomainPieces_isInternal (R : PELSplitReference) (z : PELSplitDomain R) :
    DirectSum.IsInternal (pelDomainPieces R z) :=
  isInternal_pair (pel_isCompl_eigenspaces _ (pelDomainOperator_square R z)) (by decide)

theorem pelDomainPieces_conj (R : PELSplitReference) (z : PELSplitDomain R)
    (p q : ℤ) :
    ((pelDomainPieces R z) (p, q)).map (HodgeBlocks.sigmaQ _) =
      (pelDomainPieces R z) (q, p) := by
  have hc (p q : ℤ) (x : ℂ ⊗[ℚ] HQ R.B.X 1)
      (hx : x ∈ pelDomainPieces R z (p, q)) :
      HodgeBlocks.sigmaQ _ x ∈ pelDomainPieces R z (q, p) := by
    simp only [pelDomainPieces] at hx ⊢
    split_ifs at hx with h1 h2
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      simp only [show ((0, 1) : ℤ × ℤ) ≠ (1, 0) by decide, ↓reduceIte]
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [pelDomainOperator_conj, hx, map_smulₛₗ]
      simp
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      simp only [↓reduceIte]
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [pelDomainOperator_conj, hx, map_smulₛₗ]
      simp
    · have hx0 := (Submodule.mem_bot ℂ).mp hx
      rw [hx0, map_zero]
      exact Submodule.zero_mem _
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hc p q y hy
  · intro x hx
    refine ⟨HodgeBlocks.sigmaQ _ x, hc q p x hx, ?_⟩
    exact HodgeBlocks.sigmaQ_involutive _ x

/-- The holomorphic piece is the specified negative-i period plane. -/
theorem pelDomainHodge_plane (R : PELSplitReference) (z : PELSplitDomain R) :
    pelDomainPieces R z (1, 0) = pelSplitPlane R z := by
  change Module.End.eigenspace (pelDomainOperator R z) (-Complex.I) = _
  have h := pel_matrix_negative_eigenspace
    (Algebra.TensorProduct.basis ℂ R.basis) (pelDomainOperator R z)
  simp only [pelDomainOperator, LinearMap.toMatrix_toLin] at h
  exact h.symm

local instance (R : PELSplitReference) : Module.Finite ℚ (HQ R.B.X 1) :=
  (torusCohomology_cupProductOf R.B.X).finite

/-- The rational weight-one Hodge structure attached to the matrix domain.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.1–1.3. -/
def pelDomainHodge (R : PELSplitReference) (z : PELSplitDomain R) :
    HodgeBlocks.QHodgeStructure 1 (HQ R.B.X 1) where
  H := pelDomainPieces R z
  supported pq h := by
    simp only [pelDomainPieces]
    split_ifs with h1 h2
    · subst pq; exact (h rfl).elim
    · subst pq; exact (h rfl).elim
    · rfl
  isInternal := pelDomainPieces_isInternal R z
  conj_symm := pelDomainPieces_conj R z

/-- The Hodge group in the original reference basis.
Source: Mumford, Families of abelian varieties (1966), §1. -/
def pelDomainHodgeGroup (R : PELSplitReference) (z : PELSplitDomain R) :
    Set (Matrix.GeneralLinearGroup (Fin 12) ℂ) :=
  g2_hodgeGroup (pelDomainPieces R z) (pelDomainPieces_isInternal R z) R.basis

#print axioms pelDomainHodge
end HodgeLean.Foundations.Program.GeneralTypeIII

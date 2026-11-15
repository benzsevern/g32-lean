import HodgeLean.Foundations.Program.CompensationProduct
import HodgeLean.Blocks.Weil.RationalKernel
import HodgeLean.RealDefs.CupFiltered

/-! # Definitions for the eightfold compensation stage C8 (G34 Proposition 10.2)

Definitions for `docs/specs/CompensationEightfold.md`. They are data: actual morphisms, actual
linear maps and an actual chosen cohomology class. No conclusion is stored in a definition.

* `cq8_surfaceEnd E ρ`, the map `(u, v) ↦ (u + ρu, v)` of `E ⊗ E`, and its square
  `cq8_surfaceEnd2 E ρ`, the composite used for the second surface class.
* `cq8_cross` and `cq8_crossC`: the rational cross product `pr_A^* a ∪ pr_Y^* b` and its
  scalar extension to `ℂ`, built from the complex cup product `cupC`.
* `cq8_scalarC`: the scalar extension of a rational functional, read in `ℂ`.
* `cq8_weilWitness`: a nonzero rational Weil class when one exists, and `0` otherwise. The choice
  uses no open statement; whether the class is nonzero is a theorem of the spec.

HC no distance; AV milestone no distance.
-/

set_option maxHeartbeats 400000

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

/-! ### The surface map and its square -/

/-- The surface map `(u, v) ↦ (u + ρu, v)` on `E ⊗ E`, written with the group law.
Source: G34 v1.5, proof of Proposition 10.2, "Two independent classes". -/
def cq8_surfaceEnd (E : Over (Spec ↧ℂ)) [GrpObj E] (ρ : E ⟶ E) : E ⊗ E ⟶ E ⊗ E :=
  lift (fst E E * (fst E E ≫ ρ)) (snd E E)

example (E : Over (Spec ↧ℂ)) [GrpObj E] (ρ : E ⟶ E) :
    cq8_surfaceEnd E ρ ≫ snd E E = snd E E := by
  simp only [cq8_surfaceEnd, lift_snd]

/-- The composite `cq8_surfaceEnd E ρ ≫ cq8_surfaceEnd E ρ`, the map `(u, v) ↦ ((1 + ρ)² u, v)`.
Its Weil-line eigenvalues are `(1 + ζ)²` and the conjugate, as `g34c_two_independent` uses.
Source: G34 v1.5, proof of Proposition 10.2, "Two independent classes"; the corrected C8 plan of
`docs/specs/CompensationAssembly.md` on `spec/comp2`. -/
def cq8_surfaceEnd2 (E : Over (Spec ↧ℂ)) [GrpObj E] (ρ : E ⟶ E) : E ⊗ E ⟶ E ⊗ E :=
  cq8_surfaceEnd E ρ ≫ cq8_surfaceEnd E ρ

example (E : Over (Spec ↧ℂ)) [GrpObj E] (ρ : E ⟶ E) :
    cq8_surfaceEnd2 E ρ ≫ snd E E = snd E E := by
  simp only [cq8_surfaceEnd2, cq8_surfaceEnd, Category.assoc, lift_snd]

/-! ### Rational and complex cross products -/

section Cross

variable (A Y : Over (Spec ↧ℂ))
  [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- The rational cross product `a × b = pr_A^* a ∪ pr_Y^* b` in bidegree `(i, j)`.
Source: Hatcher, *Algebraic Topology*, §3.2 and Theorem 3.15. -/
def cq8_cross (i j : ℕ) : HQ A i →ₗ[ℚ] HQ Y j →ₗ[ℚ] HQ (A ⊗ Y) (i + j) :=
  ((cupProductOf (A ⊗ Y)).cup rfl).compl₁₂
    (homPullback (fst A Y) i) (homPullback (snd A Y) j)

example (i j : ℕ) (b : HQ Y j) : cq8_cross A Y i j 0 b = 0 := by
  rw [map_zero, LinearMap.zero_apply]

/-- The complex cross product: the complex cup product `cupC` of the complexified pullbacks.
Source: Hatcher, *Algebraic Topology*, §3.2; `CupProduct.cupC`, the scalar extension of the cup
product. -/
def cq8_crossC (i j : ℕ) :
    ℂ ⊗[ℚ] HQ A i →ₗ[ℂ] ℂ ⊗[ℚ] HQ Y j →ₗ[ℂ] ℂ ⊗[ℚ] HQ (A ⊗ Y) (i + j) :=
  ((cupProductOf (A ⊗ Y)).cupC rfl).compl₁₂
    ((homPullback (fst A Y) i).baseChange ℂ) ((homPullback (snd A Y) j).baseChange ℂ)

/-- On rational vectors the complex cross product is the rational one. -/
example (i j : ℕ) (a : HQ A i) (b : HQ Y j) :
    cq8_crossC A Y i j (1 ⊗ₜ a) (1 ⊗ₜ b) = 1 ⊗ₜ cq8_cross A Y i j a b := by
  simp only [cq8_crossC, cq8_cross, LinearMap.compl₁₂_apply, LinearMap.baseChange_tmul,
    CupProduct.cupC_tmul, mul_one]

/-- The complex cross product commutes with rational conjugation, by `sigmaQ_cupC` and
`sigmaQ_baseChange`. -/
example (i j : ℕ) (a : ℂ ⊗[ℚ] HQ A i) (b : ℂ ⊗[ℚ] HQ Y j) :
    HodgeBlocks.sigmaQ _ (cq8_crossC A Y i j a b) =
      cq8_crossC A Y i j (HodgeBlocks.sigmaQ _ a) (HodgeBlocks.sigmaQ _ b) := by
  simp only [cq8_crossC, LinearMap.compl₁₂_apply, CupProduct.sigmaQ_cupC,
    HodgeBlocks.sigmaQ_baseChange]

end Cross

/-- The scalar extension of a rational functional, read in `ℂ` through `ℂ ⊗[ℚ] ℚ ≃ ℂ`.
Source: Bourbaki, *Algebra*, Chapter II, §5 (extension of scalars). -/
def cq8_scalarC {W : Type*} [AddCommGroup W] [Module ℚ W] (I : W →ₗ[ℚ] ℚ) :
    ℂ ⊗[ℚ] W →ₗ[ℂ] ℂ :=
  (Algebra.TensorProduct.rid ℚ ℂ ℂ).toLinearMap ∘ₗ I.baseChange ℂ

example {W : Type*} [AddCommGroup W] [Module ℚ W] (I : W →ₗ[ℚ] ℚ) (z : ℂ) (w : W) :
    cq8_scalarC I (z ⊗ₜ w) = (I w : ℂ) * z := by
  simp [cq8_scalarC, Algebra.smul_def]

/-- A nonzero functional stays nonzero: `ℚ` itself with the identity. -/
example : cq8_scalarC (LinearMap.id : ℚ →ₗ[ℚ] ℚ) (1 ⊗ₜ (1 : ℚ)) = 1 := by
  simp [cq8_scalarC, Algebra.TensorProduct.rid_tmul]

/-! ### A chosen rational Weil class -/

section Witness

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μc : CupProduct X} [GrpObj X]

/-- A nonzero rational Weil class of `A`, chosen when one exists, and `0` otherwise. For the
split eightfold this is the class `ξ ∈ H⁸(A × Y; ℚ)` of the C8 plan. Whether it is nonzero is not
decided here; the rank-two statement of the spec decides it.
Source: G34 v1.5, proof of Proposition 10.2 (a rational Weil class of the split eightfold); van
Geemen, *An introduction to the Hodge conjecture for abelian varieties*, LNM 1594, §4.2. -/
def cq8_weilWitness (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μc) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) :
    letI := hT.finite
    HQ X (2 * Module.finrank ℂ
      ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0))) :=
  letI := hT.finite
  open Classical in
  if h : ∃ v ∈ weilClassOf hF hB hD hT A hW, v ≠ 0 then h.choose else 0

/-- The chosen class is a rational Weil class, by construction. -/
example (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μc) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) :
    letI := hT.finite
    cq8_weilWitness hF hB hD hT A hW ∈ weilClassOf hF hB hD hT A hW := by
  let := hT.finite
  unfold cq8_weilWitness
  split_ifs with h
  · exact h.choose_spec.1
  · exact Submodule.zero_mem _

/-- When a nonzero Weil class exists, the chosen class is nonzero. -/
example (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μc) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType)
    (h : letI := hT.finite; ∃ v ∈ weilClassOf hF hB hD hT A hW, v ≠ 0) :
    letI := hT.finite
    cq8_weilWitness hF hB hD hT A hW ≠ 0 := by
  let := hT.finite
  unfold cq8_weilWitness
  split_ifs with h'
  · exact h'.choose_spec.2
  · exact absurd h h'

end Witness

end HodgeLean.Foundations.Program

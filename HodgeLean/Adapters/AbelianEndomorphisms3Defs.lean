import HodgeLean.Adapters.AbelianEndomorphisms2
import HodgeLean.Foundations.EQWCore

/-! # Endomorphisms of an abelian variety, stage 3: definitions (FROZEN)

* `hodgeEndH1 X`: the rational endomorphisms of `HQ X 1` whose complexification preserves both
  summands of the transported degree-one split `ℂ ⊗[ℚ] HQ X 1 = Hol ⊕ Anti` of `DegreeOneLattice`
  (`complexHolomorphicH1`, `complexAntiholomorphicH1`), as a `ℚ`-subalgebra of
  `Module.End ℚ (HQ X 1)`: the endomorphisms of the lattice-side rational Hodge structure.
* `latticeHodgePieces X`: the same split as a bigraded family `ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] HQ X 1)`,
  `Hol` at `(1, 0)`, `Anti` at `(0, 1)` and `⊥` elsewhere, the input shape of `hodgeLieAlgebra`.

Nothing here compares either object with de Rham or Dolbeault cohomology.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

private theorem map_baseChange_mul_le (p : Submodule ℂ (ℂ ⊗[ℚ] V))
    (S T : Module.End ℚ V) (hS : p.map (S.baseChange ℂ) ≤ p)
    (hT : p.map (T.baseChange ℂ) ≤ p) : p.map ((S * T).baseChange ℂ) ≤ p := by
  rw [LinearMap.baseChange_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  exact (Submodule.map_mono hT).trans hS

private theorem map_baseChange_add_le (p : Submodule ℂ (ℂ ⊗[ℚ] V))
    (S T : Module.End ℚ V) (hS : p.map (S.baseChange ℂ) ≤ p)
    (hT : p.map (T.baseChange ℂ) ≤ p) : p.map ((S + T).baseChange ℂ) ≤ p := by
  rw [LinearMap.baseChange_add]
  exact (Submodule.map_add_le _ _ _).trans (sup_le hS hT)

private theorem map_baseChange_algebraMap_le (p : Submodule ℂ (ℂ ⊗[ℚ] V))
    (r : ℚ) :
    p.map ((algebraMap ℚ (Module.End ℚ V) r).baseChange ℂ) ≤ p := by
  rintro _ ⟨ω, hω, rfl⟩
  rw [Module.algebraMap_end_eq_smul_id, LinearMap.baseChange_smul, LinearMap.baseChange_id,
    LinearMap.smul_apply, LinearMap.id_apply]
  exact Submodule.smul_of_tower_mem p r hω

end

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The endomorphisms of the lattice-side rational Hodge structure on `HQ X 1`: rational
endomorphisms whose complexification preserves the holomorphic and the antiholomorphic summands
of `ℂ ⊗[ℚ] HQ X 1`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 and Theorem 1.4.1
(`End_HS(H¹(X, ℚ))`); Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1
(morphisms of Hodge structures); `complexHolomorphicH1`, `complexAntiholomorphicH1`. -/
def hodgeEndH1 : Subalgebra ℚ (Module.End ℚ (HQ X 1)) where
  carrier := {T | (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X ∧
    (complexAntiholomorphicH1 X).map (T.baseChange ℂ) ≤ complexAntiholomorphicH1 X}
  mul_mem' hS hT :=
    ⟨map_baseChange_mul_le _ _ _ hS.1 hT.1, map_baseChange_mul_le _ _ _ hS.2 hT.2⟩
  add_mem' hS hT :=
    ⟨map_baseChange_add_le _ _ _ hS.1 hT.1, map_baseChange_add_le _ _ _ hS.2 hT.2⟩
  algebraMap_mem' r :=
    ⟨map_baseChange_algebraMap_le _ r, map_baseChange_algebraMap_le _ r⟩

example (T : Module.End ℚ (HQ X 1)) : T ∈ hodgeEndH1 X ↔
    (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X ∧
      (complexAntiholomorphicH1 X).map (T.baseChange ℂ) ≤ complexAntiholomorphicH1 X := Iff.rfl

-- Every endomorphism of `X` acts by an endomorphism of the lattice-side Hodge structure.
example (f : AbelianEnd X) : abelianEndAction X f ∈ hodgeEndH1 X :=
  spec_abelianEndAction_hodge X f

/-- The transported degree-one split as a bigraded family: `complexHolomorphicH1 X` in type
`(1, 0)`, `complexAntiholomorphicH1 X` in type `(0, 1)`, `⊥` in every other type.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1
(`H¹(X, ℂ) = H^{1,0} ⊕ H^{0,1}`); `spec_complexH1_split`. -/
def latticeHodgePieces (pq : ℤ × ℤ) : Submodule ℂ (ℂ ⊗[ℚ] HQ X 1) :=
  if pq = (1, 0) then complexHolomorphicH1 X
  else if pq = (0, 1) then complexAntiholomorphicH1 X else ⊥

example : latticeHodgePieces X (0, 1) = complexAntiholomorphicH1 X := by
  simp [latticeHodgePieces]

end HodgeLean.Adapters

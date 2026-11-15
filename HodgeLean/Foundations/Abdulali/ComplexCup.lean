import HodgeLean.Foundations.Abdulali.PowerDenominators
import HodgeLean.Foundations.WeilPowerHodge

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Abdulali

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

local instance : Module.Finite ℚ (HQ A 1) :=
  (torusCohomology_cupProductOf A).finite

/-- The canonical complex exterior-to-cohomology comparison.
Source: Birkenhake–Lange, Complex Abelian Varieties, 2nd ed., Lemma 1.3.1;
scalar extension of the cup-wedge isomorphism. -/
def complexCupEquiv (n : ℕ) :
    (⋀[ℂ]^n (ℂ ⊗[ℚ] HQ A 1)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A n) :=
  (WeilPower.exteriorBaseChange n).symm.trans
    (((torusCohomology_cupProductOf A).cupWedgeEquiv n).baseChange ℚ ℂ)

example (n : ℕ) : Function.Bijective (complexCupEquiv A n) :=
  (complexCupEquiv A n).bijective

/-- Scalar extension of exterior powers is natural for arbitrary rational
linear maps, including maps between different spaces.
Source: the universal property of exterior powers and scalar extension. -/
theorem exteriorBaseChange_map {V M : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] [AddCommGroup M] [Module ℚ M] [Module.Finite ℚ M]
    (n : ℕ) (f : V →ₗ[ℚ] M) :
    (WeilPower.exteriorBaseChange (V := M) n).toLinearMap.comp
      ((exteriorPower.map n f).baseChange ℂ) =
      (exteriorPower.map n (f.baseChange ℂ)).comp
        (WeilPower.exteriorBaseChange (V := V) n).toLinearMap := by
  apply (((Module.finBasis ℚ V).exteriorPower n).baseChange ℂ).ext
  intro s
  simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply,
    LinearMap.baseChange_tmul, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, WeilPower.exteriorBaseChange_one_ιMulti,
    LinearEquiv.coe_coe, Function.comp_def]

/-- Naturality of the complex cup comparison for a rational degree-one map.
The rational map in degree n is its exterior power transported by the two
cup-wedge isomorphisms.
Source: Birkenhake–Lange, Complex Abelian Varieties, Lemma 1.3.1;
scalar extension and functoriality of exterior powers. -/
theorem complexCupEquiv_naturality
    (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (n : ℕ) (f : HQ A 1 →ₗ[ℚ] HQ Y 1) (u : ℂ ⊗[ℚ] HQ A n) :
    complexCupEquiv Y n (exteriorPower.map n (f.baseChange ℂ)
      ((complexCupEquiv A n).symm u)) =
    ((((torusCohomology_cupProductOf Y).cupWedgeEquiv n).toLinearMap ∘ₗ
      exteriorPower.map n f ∘ₗ
      ((torusCohomology_cupProductOf A).cupWedgeEquiv n).symm.toLinearMap).baseChange ℂ) u := by
  letI : Module.Finite ℚ (HQ Y 1) := (torusCohomology_cupProductOf Y).finite
  have h := LinearMap.congr_fun (exteriorBaseChange_map n f)
    ((((torusCohomology_cupProductOf A).cupWedgeEquiv n).baseChange ℚ ℂ).symm u)
  have h' := congrArg (complexCupEquiv Y n) h.symm
  have h'' : complexCupEquiv Y n (exteriorPower.map n (f.baseChange ℂ)
      ((complexCupEquiv A n).symm u)) =
      (((torusCohomology_cupProductOf Y).cupWedgeEquiv n).baseChange ℚ ℂ)
        ((exteriorPower.map n f).baseChange ℂ
          ((((torusCohomology_cupProductOf A).cupWedgeEquiv n).baseChange ℚ ℂ).symm u)) := by
    simpa only [complexCupEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_symm] using h'
  rw [h'']
  clear h h' h''
  induction u using TensorProduct.inductionOn with
  | tmul c v => rfl
  | add u v hu hv => simp only [map_add, hu, hv]

end HodgeLean.Foundations.Abdulali

import HodgeLean.Foundations.Abdulali.ComplexCup
import HodgeLean.Foundations.Abdulali.SplitPowerCoordinates
import HodgeLean.Adapters.AbelianPowerHodge
import HodgeLean.Foundations.Program.MilneScalarDescent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.WeilPower HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
attribute [local irreducible] cupProductOf algebraicCycleClassSpan
variable {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  {r : ℕ}

/-- The degree-one biproduct equivalence on actual cohomology.
Source: Mac Lane, Categories for the Working Mathematician, VIII.2. -/
def powerH1Equiv (power : AbelianPowerData A Y r) :
    (HQ A 1 ⊗[ℚ] (Fin r → ℚ)) ≃ₗ[ℚ] HQ Y 1 :=
  LinearEquiv.ofLinearMap power.h1Map power.h1Inv
    (spec_g2_h1Map_comp_h1Inv power) (spec_g2_h1Inv_comp_h1Map power)

/-- Complex exterior Hodge classes map onto the complex span of the rational
Hodge classes on the specified geometric power.
Source: Birkenhake–Lange, Complex Abelian Varieties, Lemma 1.3.1 and Theorem 1.4.1. -/
theorem power_complex_hodge_image (power : AbelianPowerData A Y r) (p : ℕ) :
    letI := (torusCohomology_cupProductOf A).finite
    (exteriorHodgeClasses (abelianWeightOneHodgeStructure A).H
      (abelianWeightOneHodgeStructure A).isInternal r (2*p)).map
      ((complexCupEquiv Y (2*p)).toLinearMap.comp
        (exteriorPower.map (2*p) (power.h1Map.baseChange ℂ))) =
          (Hdg^p(Y; ℚ)).baseChange ℂ := by
  letI := (torusCohomology_cupProductOf A).finite
  letI := (torusCohomology_cupProductOf Y).finite
  rw [exteriorHodgeClasses, ← Submodule.map_comp]
  have hm : ((complexCupEquiv Y (2*p)).toLinearMap.comp
      (exteriorPower.map (2*p) (power.h1Map.baseChange ℂ))).comp
      (exteriorBaseChange (2*p)).toLinearMap =
        (power.cohomologyMap (2*p)).baseChange ℂ := by
    rw [LinearMap.comp_assoc, ← exteriorBaseChange_map]
    change ((complexCupEquiv Y (2*p)).toLinearMap.comp
      (exteriorBaseChange (2*p)).toLinearMap).comp _ = _
    have he : (complexCupEquiv Y (2*p)).toLinearMap.comp
        (exteriorBaseChange (2*p)).toLinearMap =
        (((torusCohomology_cupProductOf Y).cupWedgeEquiv (2*p)).toLinearMap).baseChange ℂ := by
      apply LinearMap.ext
      intro z
      simp only [complexCupEquiv, LinearMap.comp_apply, LinearEquiv.trans_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rfl
    rw [he, ← LinearMap.baseChange_comp]
    rfl
  rw [hm, m2_map_baseChange, spec_g2_rationalExteriorHodge_map_eq]

/-- Membership form of the complex Hodge transport on arbitrary power data.
Source: the biproduct Hodge comparison, Birkenhake–Lange, Theorem 1.4.1. -/
theorem power_complex_hodge_mem (power : AbelianPowerData A Y r) (p : ℕ)
    (v : ⋀[ℂ]^(2*p) (ℂ ⊗[ℚ] (HQ A 1 ⊗[ℚ] (Fin r → ℚ)))) :
    letI := (torusCohomology_cupProductOf A).finite
    complexCupEquiv Y (2*p) (exteriorPower.map (2*p) (power.h1Map.baseChange ℂ) v) ∈
      (Hdg^p(Y; ℚ)).baseChange ℂ ↔
    v ∈ exteriorHodgeClasses (abelianWeightOneHodgeStructure A).H
      (abelianWeightOneHodgeStructure A).isInternal r (2*p) := by
  letI := (torusCohomology_cupProductOf A).finite
  rw [← power_complex_hodge_image power p]
  have hi := ((exteriorEquiv (2*p) ((powerH1Equiv power).baseChange ℚ ℂ)).trans
    (complexCupEquiv Y (2*p))).injective
  constructor
  · rintro ⟨w, hw, he⟩
    have heq : w = v := hi he
    exact heq ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- Projection coordinates of the complexified degree-one biproduct map.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.3. -/
theorem powerH1Map_coordinates (P : AbelianPowerData A Y r)
    (x : ℂ ⊗[ℚ] HQ A 1) (u : Fin r → ℂ) :
    P.h1Map.baseChange ℂ ((powerBaseChange r).symm (x ⊗ₜ[ℂ] u)) =
      ∑ i, u i • (homPullback (P.proj i) 1).baseChange ℂ x := by
  obtain ⟨q, rfl⟩ := (multiplicityEquiv r).surjective u
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    induction q using TensorProduct.inductionOn with
    | tmul b c =>
      simp only [powerBaseChange, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
        TensorProduct.congr_symm_tmul, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
        LinearEquiv.symm_apply_apply]
      rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
      simp [AbelianPowerData.h1Map, multiplicityEquiv]
      rw [TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [TensorProduct.tmul_smul]
      rw [TensorProduct.smul_tmul']
      congr 1
      simp [smul_eq_mul, mul_comm]
    | add q₁ q₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂, Pi.add_apply,
        add_smul, Finset.sum_add_distrib]
  | add x₁ x₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂,
      map_add, smul_add, Finset.sum_add_distrib]


/-- Actual complex degree-one coordinates retaining both the power and row labels.
Source: Abdulali, Annals 155 (2002), Remark 4.2; biproduct cohomology. -/
def splitPowerH1Equiv (power : AbelianPowerData A Y r)
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1)) :
    (Fin (r*2) → Fin 6 → ℂ) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ Y 1) :=
  (splitPowerCoordinates r e).symm ≪≫ₗ (powerH1Equiv power).baseChange ℚ ℂ

end HodgeLean.Foundations.Abdulali

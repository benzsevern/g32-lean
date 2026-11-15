import HodgeLean.Foundations.Program.G32Native.WeilMarkedTorusPolarization
import HodgeLean.Foundations.Program.UniversalFamilyB60bTransport

/-! Polarization comparison for arbitrary marked abelian varieties. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations.AppellHumbert
namespace HodgeLean.Foundations.Program
variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]
  (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
  (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q)

include hQ in
/-- The Riemann form gives a nondegenerate lattice coclass.
Source: Birkenhake–Lange, §§1.3, 2.2. -/
theorem weil_riemann_lattice_nondegenerate :
    IsNondegenerate (latticeClass (b2_bilinToAddHom Q)) := by
  obtain ⟨H, hH, hE⟩ := (b2_abelian_isRiemannForm_iff X Q).1 hQ
  exact latticeClassHQ_latticeClass_nondegenerate (abelianPeriodLattice X) H hH _ hE

/-- The original lattice coclass is the cohomological polarization vector.
Source: Birkenhake–Lange, §§1.3, 2.2. -/
theorem weil_riemann_polarization_vec :
    polarizationVec (torusCohomology_cupProductOf X)
      (latticeClassHQ X (b2_bilinToAddHom Q)) =
    exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap
      (latticeClass (b2_bilinToAddHom Q)) := by
  exact ((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm_apply_apply _

/-- Comparison of the original Riemann polarization with its cohomological form.
Source: Birkenhake–Lange, §§1.3, 2.2. -/
theorem weil_riemann_polarizationForm_period  (x y : HQ X 1) :
    polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q
          hQ) x y =
      b2b_dualForm (b2_abelianLattice X) Q
        (b60b_periodLinearEquiv X x)
        (b60b_periodLinearEquiv X y) := by
  letI : FiniteDimensional ℚ (b2_abelianLattice X →+ ℚ) :=
    Module.Finite.of_basis latticeDualBasisQ
  let ep := (abelianPeriodEquiv X).symm
  have hmap := b2_abelian_nondegenerate X Q
    hQ
  change IsNondegenerate (polarizationVec
    (torusCohomology_cupProductOf X) (latticeClassHQ X (b2_bilinToAddHom Q))) at hmap
  rw [weil_riemann_polarization_vec X Q] at hmap
  have hdual := b60b_dualForm_map_equiv ep (weil_riemann_lattice_nondegenerate X Q hQ)
    hmap (abelianPeriodEquiv X x)
      (abelianPeriodEquiv X y)
  have hdual' : dualForm hmap x y = dualForm (weil_riemann_lattice_nondegenerate X Q hQ)
      (abelianPeriodEquiv X x) (abelianPeriodEquiv X y) := by
    simpa [ep] using hdual
  change dualForm (b2_abelian_nondegenerate X Q
    hQ) x y = _
  have heq : dualForm (b2_abelian_nondegenerate X Q
      hQ) = dualForm hmap :=
    b60b_dualForm_congr (weil_riemann_polarization_vec X Q)
      (b2_abelian_nondegenerate X Q hQ) hmap
  calc
    _ = dualForm hmap x y := by rw [heq]
    _ = _ := by
      rw [hdual']
      exact b60b_dualForm_latticeClass _ _ hQ.alt
        (b2bpol_flat_bijective _ _ (fun u hu ↦ b2_riemannForm_nondegenerate
          (b2_abelianF X) Q
          (b2_abelianF_isWeightOne X) hQ u hu))
        (weil_riemann_lattice_nondegenerate X Q hQ) _ _

/-- Comparison of the original Riemann polarization with its cohomological form.
Source: Birkenhake–Lange, §§1.3, 2.2. -/
theorem weil_riemann_polarizationForm_period_complex 
    (x y : ℂ ⊗[ℚ] HQ X 1) :
    (polarizationForm (torusCohomology_cupProductOf X)
      (b2_abelian_nondegenerate X Q
        hQ)).baseChange ℂ x y =
    (b2b_dualForm (b2_abelianLattice X) Q).baseChange ℂ
      ((LinearEquiv.baseChange ℚ ℂ _ _
        (b60b_periodLinearEquiv X)) x)
      ((LinearEquiv.baseChange ℚ ℂ _ _
        (b60b_periodLinearEquiv X)) y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul c x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul d y =>
      simp only [LinearMap.BilinForm.baseChange_tmul, LinearEquiv.baseChange_tmul]
      rw [weil_riemann_polarizationForm_period X Q hQ]

/-- Comparison of the original Riemann polarization with its cohomological form.
Source: Birkenhake–Lange, §§1.3, 2.2. -/
theorem weil_riemann_polarization_positive  :
    PolarizationPositive (finiteBetti_abelian X)
      (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X)
      (torusCohomology_cupProductOf X)
      (b2_abelian_nondegenerate X Q
        hQ) := by
  let S := abelianVarietyCohomologyOf (finiteBetti_abelian X)
    (spec_bettiDeRhamIso_abelian X)
    (hodgeDecomposition_of_abelian X)
    (torusCohomology_cupProductOf X)
  let E := polarizationForm (torusCohomology_cupProductOf X)
    (b2_abelian_nondegenerate X Q
      hQ)
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X)
  have hpol := b2bpol_dualForm_isPolarized (b2_abelianLattice X)
    (b2_abelianF X) Q
    (b2_abelianF_isWeightOne X) hQ
  have hmem {x : ℂ ⊗[ℚ] HQ X 1} (hx : x ∈ S.weight1.H (1, 0)) :
      ep x ∈ b2b_hodgeOne (b2_abelianLattice X)
        (b2_abelianF X) := by
    rw [← b60b_h10_period X]
    exact Submodule.mem_map_of_mem hx
  have hiso10 : ∀ x ∈ S.weight1.H (1, 0), ∀ y ∈ S.weight1.H (1, 0),
      E.baseChange ℂ x y = 0 := by
    intro x hx y hy
    rw [weil_riemann_polarizationForm_period_complex X Q hQ]
    exact hpol.riemann_first 1 _ (by simpa [b2bpol_filtration_one] using hmem hx)
      _ (by simpa [b2bpol_filtration_one] using hmem hy)
  have hiso01 : ∀ x ∈ S.weight1.H (0, 1), ∀ y ∈ S.weight1.H (0, 1),
      E.baseChange ℂ x y = 0 := by
    intro x hx y hy
    have hsx : HodgeBlocks.sigmaQ _ x ∈ S.weight1.H (1, 0) := by
      rw [← S.weight1.conj_symm 0 1]
      exact Submodule.mem_map_of_mem hx
    have hsy : HodgeBlocks.sigmaQ _ y ∈ S.weight1.H (1, 0) := by
      rw [← S.weight1.conj_symm 0 1]
      exact Submodule.mem_map_of_mem hy
    have hz := hiso10 _ hsx _ hsy
    rw [pol1_bilin_conj] at hz
    exact (map_eq_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mp hz
  apply (pol1_polarisation_iff_h10_positive S.weight1 E
    (isAlt_polarizationForm _ _) (nondegenerate_polarizationForm _ _)
    (fun pq h10 h01 ↦ by
      dsimp only [S]
      exact cohomologyHodgePiece_one_eq_bot X pq h10 h01)
    hiso10 hiso01).2
  intro x hx hx0
  rw [weil_riemann_polarizationForm_period_complex X Q hQ]
  have hepsigma : ep (HodgeBlocks.sigmaQ _ x) = HodgeBlocks.sigmaQ _ (ep x) := by
    exact HodgeBlocks.QHodgeStructure.complexificationCongr_sigmaQR
      (V := HQ X 1)
      (W := b2b_dual (b2_abelianLattice X))
      (b60b_periodLinearEquiv X) x
  rw [hepsigma]
  simpa only [HodgeBlocks.Iexp, sub_zero, zpow_one] using
    hpol.riemann_second 1 0 (by norm_num) (ep x) (by
      change ep x ∈ b2b_filtration _ (b2_abelianF X) 1 ⊓
        (b2b_filtration _ (b2_abelianF X) 0).map
          (HodgeBlocks.sigmaQ _)
      constructor
      · simpa [b2bpol_filtration_one] using hmem hx
      · refine ⟨HodgeBlocks.sigmaQ _ (ep x), ?_, ?_⟩
        · simp [b2bpol_filtration_of_le_zero]
        · exact HodgeBlocks.sigmaQR_involutive _ _) (ep.injective.ne hx0)


#print axioms weil_riemann_polarization_positive
#print axioms weil_riemann_polarizationForm_period
end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32Native.PolarizationRealComparison
import HodgeLean.Foundations.Program.G32Native.GeometricTangentEigenrank

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Module TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
open HodgeLean.RealDefs.Compare.Markman
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- Tangent multiplicities give balanced multiplicities on holomorphic cohomology.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.2 and Theorem 1.4.1;
G32 v0.18, Definition 2.1, line 136. -/
theorem printed_tangent_weil_type_aux (P : PrintedPolarizedTriple A) :
    letI := (torusCohomology_cupProductOf A).finite
    P.W.IsWeilType := by
  letI := (torusCohomology_cupProductOf A).finite
  have h3 := geometric_holomorphic_eigenrank_aux A
    (P.action QuadraticAlgebra.omega) (HodgeBlocks.WeilAction.omegaC 3)
  have hplus : finrank ℂ ↥(P.W.Vs ⊓ (abelianWeightOneHodgeStructure A).H (1, 0)) = 3 := by
    exact h3.trans P.tangent_plus
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P.W.Vs P.W.Vsbar
  have hc := HodgeBlocks.WeilAction.isCompl_Vs_Vsbar P.W (by norm_num)
  rw [hc.sup_eq_top, hc.inf_eq_bot, finrank_top, finrank_bot, add_zero,
    Module.finrank_baseChange, (torusCohomology_cupProductOf A).finrank_eq,
    P.W.finrank_Vsbar_eq_Vs, P.dim_eq] at hsum
  change 2 * finrank ℂ ↥(P.W.Vs ⊓ (abelianWeightOneHodgeStructure A).H (1, 0)) = _
  omega

/-- A rational homological Riemann form determines its degree-two cohomology class.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.3, 4.1–4.2;
`p1_isPolarization_iff` and the exterior cohomology of a torus.
The equality retains the homological form rather than introducing a scale or sign. -/
theorem printed_polarization_reconstruction_aux (P : PrintedPolarizedTriple A) :
    ∃ pol : HQ A 2,
      ∃ hω : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol),
        IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) P.W.J ∧
        PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hω ∧
        riemannForm (polarizationVec (torusCohomology_cupProductOf A) pol) = P.E := by
  letI := (torusCohomology_cupProductOf A).finite
  obtain ⟨ω, hform, -⟩ := homological_form_reconstruction P.E P.alternating
  let pol := (torusCohomology_cupProductOf A).cupWedgeEquiv 2 ω
  have hv : polarizationVec (torusCohomology_cupProductOf A) pol = ω :=
    (torusCohomology_cupProductOf A).cupWedgeEquiv 2 |>.symm_apply_apply ω
  have hpositive : p1_IsPositive ω
      (weightOneComplexStructure A (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)) := by
    constructor
    · intro x y
      simpa only [← hform, printed_real_riemann_form] using P.riemann_invariant x y
    · intro x hx
      simpa only [← hform, printed_real_riemann_form] using P.riemann_positive x hx
  have hPol : p1_IsPolarization A pol := by
    simpa only [p1_IsPolarization, hv] using hpositive
  obtain ⟨hω, hpos⟩ := (p1_isPolarization_iff A pol).1 hPol
  refine ⟨pol, hω, ?_, hpos, hv ▸ hform⟩
  rw [hv]
  apply (isRosatiSkew_iff_skew ω P.W.J).2
  intro x y
  change riemannForm ω (P.W.J.dualMap x) y = -riemannForm ω x (P.W.J.dualMap y)
  rw [hform]
  exact P.compatible x y

/-- Printed-to-cohomological polarization dictionary, in rational homology coordinates.
Source: G32 v0.18, Definition 2.1 and §2, lines 133–145; van Geemen, LNM 1594, §5.
The geometric action induces `P.W`; the polarization class is constructed from `P.E`.
The two named comparison steps above retain their separate proof obligations. -/
theorem printed_polarization_dictionary (P : PrintedPolarizedTriple A)
    (hdisc : P.discriminant = classNegTwo) :
    ∃ pol : HQ A 2,
      IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) P.W pol := by
  letI := (torusCohomology_cupProductOf A).finite
  obtain ⟨pol, hω, hR, hpos, hform⟩ := printed_polarization_reconstruction_aux P
  refine ⟨pol, ⟨P.dim_eq, printed_tangent_weil_type_aux P, hω, hR, hpos, ?_⟩⟩
  let J : {J : Module.End ℚ (HQ A 1) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id} :=
    ⟨P.W.J, P.W.J_sq⟩
  have heven : Even (finrank (QuadraticAlgebra ℚ (-3) 0) (WithJ (HQ A 1) J)) := by
    have hf := finrank_withJ J
    rw [(torusCohomology_cupProductOf A).finrank_eq, P.dim_eq] at hf
    have h6 : finrank (QuadraticAlgebra ℚ (-3) 0) (WithJ (HQ A 1) J) = 6 := by omega
    rw [h6]
    exact ⟨3, rfl⟩
  have hE : (riemannForm (polarizationVec (torusCohomology_cupProductOf A) pol)).IsAlt :=
    hform.symm ▸ P.alternating
  have hn : (riemannForm (polarizationVec (torusCohomology_cupProductOf A) pol)).Nondegenerate :=
    hform.symm ▸ P.nondegenerate
  have hd := polarization_dual_determinant J hω hR hE hn heven
  have hh : P.discriminant =
      weilDetClass (riemannForm (polarizationVec (torusCohomology_cupProductOf A) pol))
        (transposeAction J) (riemannForm_skew J hR) hE hn := by
    simp only [PrintedPolarizedTriple.discriminant, hform, J]
  exact hd.symm.trans (hh.symm.trans hdisc)

#print axioms printed_tangent_weil_type_aux
#print axioms printed_polarization_reconstruction_aux
#print axioms printed_polarization_dictionary
end HodgeLean.Foundations.Program.G32Native

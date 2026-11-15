import HodgeLean.Foundations.Program.G32Native.PELReferenceHodge
import HodgeLean.Foundations.PositivePolarizationLinear
import Mathlib.Topology.Connected.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section
set_option maxRecDepth 8000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Real complex structures compatible with the fixed quaternionic polarization.
This is a space of matrices, with the topology induced from real matrices.
Source: Abdulali, Annals 155 (2002), §2.2 and §§3.1–3.3. -/
structure PELSplitDomain (R : PELSplitReference) where
  J : Matrix (Fin 12) (Fin 12) ℝ
  square : J * J = -1
  isometry : J.transpose * R.form.map (algebraMap ℚ ℝ) * J =
    R.form.map (algebraMap ℚ ℝ)
  positive : (R.form.map (algebraMap ℚ ℝ) * J).PosDef
  commute : ∀ d, J * (R.operator d).map (algebraMap ℚ ℝ) =
    (R.operator d).map (algebraMap ℚ ℝ) * J

instance (R : PELSplitReference) : TopologicalSpace (PELSplitDomain R) :=
  TopologicalSpace.induced PELSplitDomain.J inferInstance

/-- The negative-i eigenspace in reference coordinates (the Siegel sign convention).
Source: Birkenhake–Lange, §§1.1–1.3. -/
def pelSplitPlane (R : PELSplitReference) (z : PELSplitDomain R) :
    Submodule ℂ (ℂ ⊗[ℚ] HQ R.B.X 1) :=
  (LinearMap.ker (Matrix.toLin' (z.J.map (algebraMap ℝ ℂ)) +
    Complex.I • (LinearMap.id : Module.End ℂ (Fin 12 → ℂ)))).map
      (Algebra.TensorProduct.basis ℂ R.basis).equivFun.symm.toLinearMap

/-- Extract the reference complex structure from its actual polarized Hodge plane.
Source: Birkenhake–Lange, §§1.1–1.3, 4.2, 9.6;
Abdulali, Annals 155 (2002), §2.2. -/
theorem pel_reference_complex_structure_aux (R : PELSplitReference) :
    ∃ z : PELSplitDomain R, pelSplitPlane R z = complexHolomorphicH1 R.B.X := by
  let X := R.B.X
  let hF := finiteBetti_abelian X
  let hB := spec_bettiDeRhamIso_abelian X
  let I := weightOneComplexStructure X hF hB
  let b := Algebra.TensorProduct.basis ℝ R.basis
  let E := polarizationForm (torusCohomology_cupProductOf X) R.polarized.nondegenerate
  have hI : ∀ x, I (I x) = -x := (spec_weightOneComplexStructure X hF hB).1
  have hpos := (spec_polarizationPositive_iff X hF hB R.polarized.nondegenerate).mp
    R.polarized.positive
  have hinv : ∀ x y, E.baseChange ℝ (I x) (I y) = E.baseChange ℝ x y :=
    ((spec_firstRiemannRelation X hF hB R.polarized.nondegenerate).mp hpos.1).2
  have hform : LinearMap.toMatrix₂ b b (E.baseChange ℝ) =
      R.form.map (algebraMap ℚ ℝ) := pel_form_matrix_real R.basis E
  let J := LinearMap.toMatrix b b I
  have hJ : J * J = -1 := pel_square_matrix b I hI
  have hiso : J.transpose * R.form.map (algebraMap ℚ ℝ) * J =
      R.form.map (algebraMap ℚ ℝ) := by
    rw [← hform]
    exact pel_isometry_matrix b (E.baseChange ℝ) I hinv
  have hp : (R.form.map (algebraMap ℚ ℝ) * J).PosDef := by
    rw [← hform, ← LinearMap.toMatrix₂_compl₂ b b]
    apply pel_positive_matrix
    · exact pel_twisted_form_symmetric (E.baseChange ℝ) I
        (p1l_dualForm_real_skew R.polarized.nondegenerate) hI hinv
    · exact hpos.2
  have hc : ∀ d, J * (R.operator d).map (algebraMap ℚ ℝ) =
      (R.operator d).map (algebraMap ℚ ℝ) * J := by
    intro d
    have h := p1r_baseChange_comp_weightOneComplexStructure X
      (spec_g4_abelianEnd0Action_mem_hodgeEndH1 X (R.end0 d))
    have hm := congrArg (LinearMap.toMatrix b b) h.symm
    change LinearMap.toMatrix b b (I *
      ((abelianEnd0Action X (R.end0 d)).unop.baseChange ℝ)) =
      LinearMap.toMatrix b b (((abelianEnd0Action X (R.end0 d)).unop.baseChange ℝ) * I) at hm
    simpa only [J, b, X, PELSplitReference.operator, LinearMap.toMatrix_mul,
      LinearMap.toMatrix_baseChange] using hm
  refine ⟨⟨J, hJ, hiso, hp, hc⟩, ?_⟩
  change (LinearMap.ker (Matrix.toLin' (J.map (algebraMap ℝ ℂ)) +
    Complex.I • (LinearMap.id : Module.End ℂ (Fin 12 → ℂ)))).map
      (Algebra.TensorProduct.basis ℂ R.basis).equivFun.symm.toLinearMap = _
  rw [← pel_matrix_complexification R.basis I, pel_matrix_negative_eigenspace]
  exact pel_holomorphic_negative_eigenspace X

/-- The retained reference point of the quaternionic period space. -/
def pelSplitReferencePoint (R : PELSplitReference) : PELSplitDomain R :=
  Classical.choose (pel_reference_complex_structure_aux R)

/-- One connected component of the full polarized quaternionic period space.
Source: Abdulali, Annals 155 (2002), §§2.2–2.3, 3.2. -/
abbrev PELSplitComponent (R : PELSplitReference) :=
  {z : PELSplitDomain R // z ∈ connectedComponent (pelSplitReferencePoint R)}

/-- The base point remains in the retained component. -/
def pelSplitBasePoint (R : PELSplitReference) : PELSplitComponent R :=
  ⟨pelSplitReferencePoint R, mem_connectedComponent⟩

#print axioms pel_reference_complex_structure_aux
end HodgeLean.Foundations.Program.GeneralTypeIII

import HodgeLean.Adapters.PolarizedHodgeAbelianProofs
import HodgeLean.Foundations.EQWCore

/-!
# Polarized weight-one Hodge structures on abelian varieties (FROZEN SPEC)

This specification isolates implications from the weight-one Hodge decomposition supplied by
the abelian cup-left comparison and from an explicitly bound positive polarization. It does not
construct an ample line bundle, prove Lefschetz theorems, or prove reductivity. The dictionary
statement is an implication from the existing abelian Hodge package. HC no distance; AV
milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

namespace HodgeLean.Adapters

open HodgeLean.Foundations HodgeLean.RealDefs HodgeBlocks
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
  HodgeLean.Foundations.HermitianForm HodgeLean.Foundations.WeilPower
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Module
open scoped TensorProduct

/-- The abelian weight-one Hodge decomposition admits a real complex structure whose
complexification is `-C`; for `0 < d` it supplies the Weil signature dictionary.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Ch. 1 and Ch. 4, §4.1--4.2;
van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5. -/
theorem spec_exists_weightOneComplexStructure_dictionary
    (X : CategoryTheory.Over (AlgebraicGeometry.Spec ↧ℂ)) [CategoryTheory.GrpObj X]
    [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.Smooth X.hom]
    [AlgebraicGeometry.IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    ∃ I : ℝ ⊗[ℚ] HQ X 1 →ₗ[ℝ] ℝ ⊗[ℚ] HQ X 1,
      (∀ x, I (I x) = -x) ∧
      complexifyRealEnd I =
        -gradingOperator (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
          (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal ∧
      ∀ {d : ℚ} (_hd : 0 < d) (A : letI := hT.finite
        WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d),
        SignatureDictionary hF hB hD hT A I :=
  spec_exists_weightOneComplexStructure_dictionary_aux X hF hB

/-- The canonical real weight-one complex structure, selected from the `-C` characterization.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Ch. 1;
van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5. -/
noncomputable def weightOneComplexStructure
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X) :
    ℝ ⊗[ℚ] HQ X 1 →ₗ[ℝ] ℝ ⊗[ℚ] HQ X 1 :=
  Classical.choose (spec_exists_weightOneComplexStructure_dictionary X hF hB)

/-- The square, complexification, and dictionary characterizing the canonical operator. -/
theorem spec_weightOneComplexStructure
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    (∀ x, weightOneComplexStructure X hF hB
      (weightOneComplexStructure X hF hB x) = -x) ∧
    complexifyRealEnd (weightOneComplexStructure X hF hB) =
      -gradingOperator (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal ∧
    ∀ {d : ℚ} (_hd : 0 < d) (A : letI := hT.finite
      WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d),
      SignatureDictionary hF hB hD hT A (weightOneComplexStructure X hF hB) :=
  Classical.choose_spec (spec_exists_weightOneComplexStructure_dictionary X hF hB)

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X) :
    ∀ x, weightOneComplexStructure X hF hB
      (weightOneComplexStructure X hF hB x) = -x :=
  (spec_weightOneComplexStructure X hF hB).1

/-- Hodge type, equal-type isotropy, and invariance under the canonical complex structure are
the three forms of the first Riemann relation. -/
theorem spec_firstRiemannRelation
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {η : HQ X 2} (hω : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) η)) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    let S := abelianVarietyCohomologyOf hF hB hD hT
    let I := weightOneComplexStructure X hF hB
    ((η : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ)) ↔
      (((∀ x ∈ S.weight1.H (1, 0), ∀ y ∈ S.weight1.H (1, 0),
          (polarizationForm hT hω).baseChange ℂ x y = 0) ∧
        (∀ x ∈ S.weight1.H (0, 1), ∀ y ∈ S.weight1.H (0, 1),
          (polarizationForm hT hω).baseChange ℂ x y = 0)) ∧
       (∀ x y, (polarizationForm hT hω).baseChange ℝ (I x) (I y) =
          (polarizationForm hT hω).baseChange ℝ x y)) :=
  spec_firstRiemannRelation_aux X hF hB hω (weightOneComplexStructure X hF hB)
    (spec_weightOneComplexStructure X hF hB).2.1

/-- Positivity is the first Riemann relation plus positive definiteness of `E(x,Ix)`. -/
theorem spec_polarizationPositive_iff
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {η : HQ X 2} (hω : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) η)) :
    let hT := torusCohomology_cupProductOf X
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    PolarizationPositive hF hB hD hT hω ↔
      ((η : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ) ∧ ∀ x, x ≠ 0 →
        0 < (polarizationForm hT hω).baseChange ℝ x (weightOneComplexStructure X hF hB x)) :=
  spec_polarizationPositive_iff_aux X hF hB hω (weightOneComplexStructure X hF hB)
    (spec_weightOneComplexStructure X hF hB).2.1

/-- G32 assembly: for a polarized abelian sixfold, Weil type is exactly Hermitian signature
`(3,3)`; the canonical `I`, its square, commutation, positivity, and dictionary are discharged. -/
theorem spec_isWeilType_iff_hermSignature_eq
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {d : ℚ} (hd : 0 < d) [Fact (∀ r : ℚ, r ^ 2 ≠ -d + 0 * r)]
    (hdim : dim X.left = 6)
    (A : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    {η : HQ X 2} (hω : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) η))
    (hR : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      IsRosatiSkew (polarizationVec hT η) A.J)
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT hω) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    A.IsWeilType ↔
      hermSignature (weilHermitian (polarizationForm hT hω) ⟨A.J, A.J_sq⟩
        (polarizationForm_skew hT hω hR)) = (3, 3) :=
  spec_isWeilType_iff_hermSignature_eq_aux X hF hB hd hdim A hω hR hpos

/-- A positive polarization makes both equal-type weight-one Hodge pieces isotropic for its
rational alternating form (the first Riemann relation).
Source: Carlson--Müller-Stach--Peters, *Period Mappings and Period Domains*, Def. 3.1.8;
Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Ch. 4, §4.1. -/
theorem spec_polarizationPositive_isotropic
    (X : CategoryTheory.Over (AlgebraicGeometry.Spec ↧ℂ)) [CategoryTheory.GrpObj X]
    [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.Smooth X.hom]
    [AlgebraicGeometry.IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {η : HQ X 2} (hω : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) η))
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT hω) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    let S := abelianVarietyCohomologyOf hF hB hD hT
    (∀ x ∈ S.weight1.H (1, 0), ∀ y ∈ S.weight1.H (1, 0),
      (polarizationForm hT hω).baseChange ℂ x y = 0) ∧
    (∀ x ∈ S.weight1.H (0, 1), ∀ y ∈ S.weight1.H (0, 1),
      (polarizationForm hT hω).baseChange ℂ x y = 0) :=
  spec_polarizationPositive_isotropic_aux X hF hB hω hpos

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {η : HQ X 2} (hω : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) η))
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT hω) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    let S := abelianVarietyCohomologyOf hF hB hD hT
    ∀ x ∈ S.weight1.H (1, 0), ∀ y ∈ S.weight1.H (1, 0),
      (polarizationForm hT hω).baseChange ℂ x y = 0 :=
  (spec_polarizationPositive_isotropic X hF hB hω hpos).1

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {η : HQ X 2} (hω : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) η))
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT hω) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    let S := abelianVarietyCohomologyOf hF hB hD hT
    let E := polarizationForm hT hω
    ∀ (hdim : Module.finrank ℚ (HQ X 1) = 12 ∨ Module.finrank ℚ (HQ X 1) = 16)
      (hE : E.Nondegenerate) (hAlt : E.IsAlt)
      (J : Module.End ℚ (HQ X 1)) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
      (hskew : ∀ x y, E (J x) y = -E x (J y))
      (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → S.weight1.H pq = ⊥)
      (hJH : ∀ pq, ∀ x ∈ S.weight1.H pq, J.baseChange ℂ x ∈ S.weight1.H pq)
      (hbalPos : Module.finrank ℂ ↥(S.weight1.H (1, 0) ⊓
          Module.End.eigenspace (J.baseChange ℂ) root) =
        Module.finrank ℂ ↥(S.weight1.H (0, 1) ⊓
          Module.End.eigenspace (J.baseChange ℂ) root))
      (hbalNeg : Module.finrank ℂ ↥(S.weight1.H (1, 0) ⊓
          Module.End.eigenspace (J.baseChange ℂ) (-root)) =
        Module.finrank ℂ ↥(S.weight1.H (0, 1) ⊓
          Module.End.eigenspace (J.baseChange ℂ) (-root)))
      (hred : LieAlgebra.radical ℚ (hodgeLieAlgebra S.weight1.H S.weight1.isInternal) =
        LieAlgebra.center ℚ (hodgeLieAlgebra S.weight1.H S.weight1.isInternal))
      (hcomm : Subalgebra.centralizer ℚ
          (hodgeLieAlgebra S.weight1.H S.weight1.isInternal : Set (Module.End ℚ (HQ X 1))) =
        Algebra.adjoin ℚ {J})
      (hclass : EQWClassification E hE J hJ hskew),
      complexSpan (hodgeLieAlgebra S.weight1.H S.weight1.isInternal).toSubmodule =
        (complexSU E hE J hJ hskew).toSubmodule := by
  dsimp only
  letI := (torusCohomology_cupProductOf X).finite
  intro hdim hE hAlt J hJ hskew hsupp hJH hbalPos hbalNeg hred hcomm hclass
  exact spec_eqw_hSU_of_centralizer_eq hdim _ hE hAlt J hJ hskew hsupp hJH
    (spec_polarizationPositive_isotropic X hF hB hω hpos).1
    (spec_polarizationPositive_isotropic X hF hB hω hpos).2
    hbalPos hbalNeg hred hcomm hclass

/-- On a positive-dimensional abelian variety, reversing a positive polarization reverses its
positivity, so the negative class cannot be positive when both associated alternating forms are
nondegenerate.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Ch. 4, §4.1--4.2. -/
theorem spec_neg_not_polarizationPositive
    (X : CategoryTheory.Over (AlgebraicGeometry.Spec ↧ℂ)) [CategoryTheory.GrpObj X]
    [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.Smooth X.hom]
    [AlgebraicGeometry.IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hdim : 0 < dim X.left)
    {η : HQ X 2}
    (hω : Symplectic.IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X) η))
    (hωneg : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) (-η)))
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT hω) :
    let hT := torusCohomology_cupProductOf X
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    ¬ PolarizationPositive hF hB hD hT hωneg :=
  spec_neg_not_polarizationPositive_aux X hF hB hdim hω hωneg hpos

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hdim : 0 < dim X.left)
    {η : HQ X 2}
    (hω : Symplectic.IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X) η))
    (hωneg : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) (-η)))
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT hω) :
    let hT := torusCohomology_cupProductOf X
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    ¬ PolarizationPositive hF hB hD hT hωneg :=
  spec_neg_not_polarizationPositive X hF hB hdim hω hωneg hpos

/-- The first coordinate line in the standard rational symplectic plane is its own orthogonal.
It is therefore the concrete obstruction showing that symplectic invariance alone does not give
an orthogonal complement; positivity is essential in complete-reducibility arguments.
Source: Moonen, *An introduction to Mumford--Tate groups* (2004), §1--2. -/
theorem spec_pol1IsotropicLine_orthogonal :
    pol1StandardSymplectic.orthogonal pol1IsotropicLine = pol1IsotropicLine :=
  spec_pol1IsotropicLine_orthogonal_aux

example : pol1StandardSymplectic.orthogonal pol1IsotropicLine = pol1IsotropicLine :=
  spec_pol1IsotropicLine_orthogonal

/-! The next three statements expose the canonical complex operator `-C`.  On a weight-one
Hodge structure it is the complexification of the real complex structure with the convention
fixed above. -/

/-- The canonical weight-one complex operator has eigenvalue `-i` on `H^{1,0}`.
Source: Deligne, *Théorie de Hodge II*, §2.1; Birkenhake--Lange, Ch. 1. -/
theorem spec_weightOneComplexOperator_h10
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (x : ℂ ⊗[ℚ] V) (hx : x ∈ M.H (1, 0)) :
    (-gradingOperator M.H M.isInternal) x = -Complex.I • x :=
  spec_weightOneComplexOperator_h10_aux M x hx

example {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (x : ℂ ⊗[ℚ] V) (hx : x ∈ M.H (1, 0)) :
    x ∈ Module.End.eigenspace (-gradingOperator M.H M.isInternal) (-Complex.I) := by
  rw [Module.End.mem_eigenspace_iff]
  exact spec_weightOneComplexOperator_h10 M x hx

/-- The canonical weight-one complex operator has eigenvalue `+i` on `H^{0,1}`.
Source: Deligne, *Théorie de Hodge II*, §2.1; Birkenhake--Lange, Ch. 1. -/
theorem spec_weightOneComplexOperator_h01
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (x : ℂ ⊗[ℚ] V) (hx : x ∈ M.H (0, 1)) :
    (-gradingOperator M.H M.isInternal) x = Complex.I • x :=
  spec_weightOneComplexOperator_h01_aux M x hx

example {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (x : ℂ ⊗[ℚ] V) (hx : x ∈ M.H (0, 1)) :
    (-gradingOperator M.H M.isInternal) x = Complex.I • x :=
  spec_weightOneComplexOperator_h01 M x hx

/-- Every rational Hodge endomorphism commutes after complexification with the canonical
weight-one complex operator; this applies in particular to the `J` of every `WeilAction`.
Source: Deligne, *Théorie de Hodge II*, §2.1. -/
theorem spec_weightOneComplexOperator_commutes
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (T : M.Hom M) (x : ℂ ⊗[ℚ] V) :
    (-gradingOperator M.H M.isInternal) (T.toLinearMap.baseChange ℂ x) =
      T.toLinearMap.baseChange ℂ ((-gradingOperator M.H M.isInternal) x) :=
  spec_weightOneComplexOperator_commutes_aux M T x

example {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (T : M.Hom M) :
    (-gradingOperator M.H M.isInternal).comp (T.toLinearMap.baseChange ℂ) =
      (T.toLinearMap.baseChange ℂ).comp (-gradingOperator M.H M.isInternal) := by
  apply LinearMap.ext
  intro x
  exact spec_weightOneComplexOperator_commutes M T x

/-- The first Riemann relation forces every element of the weight-one Hodge Lie algebra to be
infinitesimally symplectic for its rational alternating form.
Source: Deligne, *Théorie de Hodge II*, §2.1; Moonen, *An introduction to Mumford--Tate groups*,
§1--2. -/
theorem spec_polarization_hodgeLieAlgebra_skew
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {A : Module.End ℚ (HQ X 1)} {x y : HQ X 1} {eta : HQ X 2}
    (homega : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) eta))
    (hfirst : (eta : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ))
    (hA : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      A ∈ hodgeLieAlgebra (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    polarizationForm hT homega (A x) y = -polarizationForm hT homega x (A y) :=
  spec_polarization_hodgeLieAlgebra_skew_aux X hF hB homega hfirst hA

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {A : Module.End ℚ (HQ X 1)} {x : HQ X 1} {eta : HQ X 2}
    (homega : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) eta))
    (hfirst : (eta : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ))
    (hA : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      A ∈ hodgeLieAlgebra (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    polarizationForm hT homega (A x) x = -polarizationForm hT homega x (A x) :=
  spec_polarization_hodgeLieAlgebra_skew X hF hB homega hfirst hA

/-- Under a positive polarization, the `E`-orthogonal of every Hodge-Lie-stable rational
subspace is a stable complementary subspace.
Source: Deligne, *Théorie de Hodge II*, §2.1; Moonen, *An introduction to Mumford--Tate groups*,
§1--2. -/
theorem spec_polarization_orthogonal_stable_complement
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {eta : HQ X 2} (homega : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) eta))
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT homega)
    (W : Submodule ℚ (HQ X 1))
    (hW : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      ∀ A ∈ hodgeLieAlgebra (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal, W.map A ≤ W) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    let L := hodgeLieAlgebra (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
      (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal
    let Wperp := (polarizationForm hT homega).orthogonal W
    (∀ A ∈ L, Wperp.map A ≤ Wperp) ∧ W ⊓ Wperp = ⊥ ∧ W ⊔ Wperp = ⊤ :=
  spec_polarization_orthogonal_stable_complement_aux X hF hB homega hpos W hW

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {eta : HQ X 2} (homega : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) eta))
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT homega)
    (W : Submodule ℚ (HQ X 1)) (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤)
    (hW : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      ∀ A ∈ hodgeLieAlgebra (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal, W.map A ≤ W) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let Wperp := (polarizationForm hT homega).orthogonal W
    W ≠ ⊥ ∧ W ≠ ⊤ ∧ W ⊓ Wperp = ⊥ ∧ W ⊔ Wperp = ⊤ := by
  have h := spec_polarization_orthogonal_stable_complement X hF hB homega hpos W hW
  exact ⟨hW0, hW1, h.2.1, h.2.2⟩

end HodgeLean.Adapters

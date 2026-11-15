import HodgeLean.Foundations.Program.CyclotomicWeilProofs

/-! # Cyclotomic determinant classes

Implications from a free cyclotomic action and balanced signature on degree-one cohomology.
The determinant carrier is defined using primitive eigenspaces and rational descent.
No algebraicity theorem of Schoen or supplier construction is asserted here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers

namespace HodgeLean.Foundations

/-- Each primitive eigenspace has field rank many dimensions; its determinant is a line, and these lines form a direct sum.
Source: G32 v0.16, Section 4.1; separable scalar extension of a free field module. -/
theorem cyc_eigenline_decomposition {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {m h : ℕ} (hm : 3 ≤ m) (hh : 0 < h)
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    (∀ t : cyc_Field m →ₐ[ℚ] ℂ,
      Module.finrank ℂ ↥(cyc_eigenspace e t) = h ∧
        Module.finrank ℂ ↥(cyc_line e t) = 1) ∧
      iSupIndep (cyc_line e) :=
  cyc_eigenline_decomposition_aux hm hh e

example {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {m h : ℕ} (hm : 3 ≤ m) (hh : 0 < h)
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    (∀ t : cyc_Field m →ₐ[ℚ] ℂ,
      Module.finrank ℂ ↥(cyc_eigenspace e t) = h ∧
        Module.finrank ℂ ↥(cyc_line e t) = 1) ∧
      iSupIndep (cyc_line e) :=
  cyc_eigenline_decomposition hm hh e

/-- Scalar extension of the rational determinant carrier recovers every primitive determinant line.
Source: G32 v0.16, Section 4.1, the identity for W_F; Galois descent over the cyclotomic splitting field. -/
theorem cyc_descent {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {m h : ℕ} (hm : 3 ≤ m) (hh : 0 < h)
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    ((cyc_wedges e).baseChange ℂ).map
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) h).toLinearMap =
        cyc_topLines e :=
  cyc_descent_aux hm hh e

example {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {m h : ℕ} (hm : 3 ≤ m) (hh : 0 < h)
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    ((cyc_wedges e).baseChange ℂ).map
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) h).toLinearMap =
        cyc_topLines e :=
  cyc_descent hm hh e

/-- The rational determinant carrier has rank equal to the number of primitive embeddings.
Source: G32 v0.16, Section 4.1; Schoen (1988), Section 1. -/
theorem cyc_rational_rank {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {m h : ℕ} (hm : 3 ≤ m) (hh : 0 < h)
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    Module.finrank ℚ ↥(cyc_wedges e) = m.totient :=
  cyc_rational_rank_aux hm hh e

example {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {m h : ℕ} (hm : 3 ≤ m) (hh : 0 < h)
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    Module.finrank ℚ ↥(cyc_wedges e) = m.totient :=
  cyc_rational_rank hm hh e

/-- The cup image of the determinant carrier has the same positive rational rank.
Source: G32 v0.16, Section 4.1; Birkenhake–Lange, Complex Abelian Varieties, Lemma 1.3.1. -/
theorem cyc_cohomology_rank {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [GrpObj X] {μ : CupProduct X}
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {m k : ℕ}
    (A : letI := hT.finite
      cyc_Action (abelianVarietyCohomologyOf hF hB hD hT).weight1 m k) :
    letI := hT.finite;
    Module.finrank ℚ ↥(cyc_classSpace μ A.cyc_coordinates) = m.totient :=
  cyc_cohomology_rank_aux hF hB hD hT A

example {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [GrpObj X] {μ : CupProduct X}
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {m k : ℕ}
    (A : letI := hT.finite
      cyc_Action (abelianVarietyCohomologyOf hF hB hD hT).weight1 m k) :
    letI := hT.finite;
    Module.finrank ℚ ↥(cyc_classSpace μ A.cyc_coordinates) = m.totient :=
  cyc_cohomology_rank hF hB hD hT A

/-- Balanced signature puts every determinant class in Hodge type (k,k).
Source: G32 v0.16, Section 4.1; Schoen (1988), Section 1; Voisin, Hodge Theory I, Section 7.1. -/
theorem cyc_classes_hodge {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [GrpObj X] {μ : CupProduct X}
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {m k : ℕ}
    (A : letI := hT.finite
      cyc_Action (abelianVarietyCohomologyOf hF hB hD hT).weight1 m k)
    (hC : CupFiltered X μ) :
    letI := hT.finite;
    cyc_classSpace μ A.cyc_coordinates ≤ Hdg^k(X; ℚ) :=
  cyc_classes_hodge_aux hF hB hD hT A hC

example {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [GrpObj X] {μ : CupProduct X}
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {m k : ℕ}
    (A : letI := hT.finite
      cyc_Action (abelianVarietyCohomologyOf hF hB hD hT).weight1 m k)
    (hC : CupFiltered X μ) :
    letI := hT.finite;
    cyc_classSpace μ A.cyc_coordinates ≤ Hdg^k(X; ℚ) :=
  cyc_classes_hodge hF hB hD hT A hC

/-- For orders three and six the cyclotomic carrier agrees with the quadratic carrier, including algebraicity.
Source: G32 v0.16, Section 4.1; van Geemen (1994), Section 4.2; RealDefs.weilClassOf. -/
theorem cyc_quadratic_comparison {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [GrpObj X] {μ : CupProduct X}
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {m k : ℕ}
    (A : letI := hT.finite
      cyc_Action (abelianVarietyCohomologyOf hF hB hD hT).weight1 m k)
    (hm : m = 3 ∨ m = 6) (u : cyc_Field m) (hu : u ^ 2 = -3)
    (B : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    (hW : letI := hT.finite; B.IsWeilType)
    (hJ : letI := hT.finite; B.J = cyc_scalar A.cyc_coordinates u) :
    letI := hT.finite;
    HEq (cyc_classSpace μ A.cyc_coordinates) (weilClassOf hF hB hD hT B hW) ∧
      (cyc_Algebraic μ A.cyc_coordinates ↔ WeilClassesAlgebraic hF hB hD hT B hW) :=
  cyc_quadratic_comparison_aux hF hB hD hT A hm u hu B hW hJ

example {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [GrpObj X] {μ : CupProduct X}
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {m k : ℕ}
    (A : letI := hT.finite
      cyc_Action (abelianVarietyCohomologyOf hF hB hD hT).weight1 m k)
    (hm : m = 3 ∨ m = 6) (u : cyc_Field m) (hu : u ^ 2 = -3)
    (B : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    (hW : letI := hT.finite; B.IsWeilType)
    (hJ : letI := hT.finite; B.J = cyc_scalar A.cyc_coordinates u) :
    letI := hT.finite;
    HEq (cyc_classSpace μ A.cyc_coordinates) (weilClassOf hF hB hD hT B hW) ∧
      (cyc_Algebraic μ A.cyc_coordinates ↔ WeilClassesAlgebraic hF hB hD hT B hW) :=
  cyc_quadratic_comparison hF hB hD hT A hm u hu B hW hJ

/-- The quadratic supplier predicate is the order-three or order-six specialization on the G32 carrier.
Source: G32 v0.16, Section 4.1; Papers.G32TransferDefs, g32t_WeilAlg. -/
theorem cyc_g32_bridge (P : g32t_Sixfold) {m k : ℕ}
    (A : letI := (torusCohomology_cupProductOf P.X).finite
      cyc_Action (abelianVarietyCohomologyOf (finiteBetti_abelian P.X)
        (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
        (torusCohomology_cupProductOf P.X)).weight1 m k)
    (hm : m = 3 ∨ m = 6) (u : cyc_Field m) (hu : u ^ 2 = -3)
    (hW : letI := (torusCohomology_cupProductOf P.X).finite; P.W.IsWeilType)
    (hJ : letI := (torusCohomology_cupProductOf P.X).finite; P.W.J = cyc_scalar A.cyc_coordinates u) :
    letI := (torusCohomology_cupProductOf P.X).finite;
    cyc_Algebraic (cupProductOf P.X) A.cyc_coordinates ↔ g32t_WeilAlg P :=
  cyc_g32_bridge_aux P A hm u hu hW hJ

example (P : g32t_Sixfold) {m k : ℕ}
    (A : letI := (torusCohomology_cupProductOf P.X).finite
      cyc_Action (abelianVarietyCohomologyOf (finiteBetti_abelian P.X)
        (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
        (torusCohomology_cupProductOf P.X)).weight1 m k)
    (hm : m = 3 ∨ m = 6) (u : cyc_Field m) (hu : u ^ 2 = -3)
    (hW : letI := (torusCohomology_cupProductOf P.X).finite; P.W.IsWeilType)
    (hJ : letI := (torusCohomology_cupProductOf P.X).finite; P.W.J = cyc_scalar A.cyc_coordinates u) :
    letI := (torusCohomology_cupProductOf P.X).finite;
    cyc_Algebraic (cupProductOf P.X) A.cyc_coordinates ↔ g32t_WeilAlg P :=
  cyc_g32_bridge P A hm u hu hW hJ

end HodgeLean.Foundations

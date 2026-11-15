import HodgeLean.Foundations.BundleThom.InverseFrameEvaluationHelpers
import HodgeLean.Foundations.BundleThom.ConormalFrameRestrictionHelpers

/-! # Inverse normal coordinates for all local section domains

The actual frame and arbitrary section are compared on their common scheme open.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle
namespace HodgeLean.Foundations.BundleThom

/-- Inverse normal-frame evaluation is continuous for sections on any supplied scheme open.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, restriction and analytification of dual frames. -/
theorem i1_normalFrameInverse_evaluation_onOpen_continuous
    {Q : Over (Spec ↧ℂ)} {Z : Scheme} (j : Q.left ⟶ Z) (k : ℕ)
    (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (W : Q.left.Opens)
    (s : SheafOfModules.unit.{0} W.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback W.ι).obj (Conormal.sheaf j)) :
    Continuous (fun p : {p : ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ) |
        p.1.1 ∈ Point.overOpen W} =>
      ((i1_normalFrameEquiv j k U E).symm p.1).1.2
        (i1_conormalSectionValue j W s p.1.1.1 p.2)) := by
  let P := {p : ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ) |
    p.1.1 ∈ Point.overOpen W}
  let K := U ⊓ W
  have hKU : K ≤ U := inf_le_left
  have hKW : K ≤ W := inf_le_right
  let EK := i1_conormalFrameRestriction j k hKU E
  let sK := i1_localModuleSectionRestriction (Conormal.sheaf j) hKW s
  let g : P → ↥(Point.overOpen K : Set (ComplexPoint Q)) × (Fin k → ℂ) :=
    fun p => (⟨p.1.1.1, ⟨p.1.1.2, p.2⟩⟩, p.1.2)
  have hP : Continuous (fun p : P => p.1) := continuous_subtype_val
  have hU : Continuous (fun p : P => p.1.1) := continuous_fst.comp hP
  have hbase : Continuous (fun p : P => p.1.1.1) := continuous_subtype_val.comp hU
  have hK : Continuous (fun p : P =>
      (⟨p.1.1.1, ⟨p.1.1.2, p.2⟩⟩ : ↥(Point.overOpen K : Set (ComplexPoint Q)))) :=
    hbase.subtype_mk (fun p => ⟨p.1.1.2, p.2⟩)
  have hvec : Continuous (fun p : P => p.1.2) := continuous_snd.comp hP
  have hg : Continuous g := hK.prodMk hvec
  have hc := i1_normalFrameInverse_evaluation_continuous j k K EK sK
  apply (hc.comp hg).congr
  intro p
  have hxK : p.1.1.1 ∈ Point.overOpen K := ⟨p.1.1.2, p.2⟩
  have hb := i1_conormalFrameBasis_restriction j k hKU E p.1.1.1 hxK
  have hm := i1_conormalSectionValue_restriction j hKW s p.1.1.1 hxK
  have ht := congrArg (fun b : Module.Basis (Fin k) ℂ (i1_conormalFibre j p.1.1.1) =>
    b.dualBasis.equivFun.symm p.1.2 (i1_conormalSectionValue j W s p.1.1.1 p.2)) hb
  exact (congrArg
    ((i1_conormalFrameBasis j k K EK p.1.1.1 hxK).dualBasis.equivFun.symm p.1.2) hm).trans ht

variable {Q : Over (Spec ↧ℂ)} {Z : Scheme} (j : Q.left ⟶ Z) (k : ℕ)
private local instance : TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- The inverse actual frame equivalence is continuous for the specified normal total topology.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, analytification of local normal coordinates. -/
theorem i1_normalFrameEquiv_symm_continuous (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k)) :
    Continuous (i1_normalFrameEquiv j k U E).symm := by
  let P := ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ)
  let f : P → TotalSpace (Fin k → ℂ) (i1_normalFibre j) :=
    fun p => ((i1_normalFrameEquiv j k U E).symm p).1
  have hb : Continuous (fun p : P => (f p).proj) :=
    continuous_subtype_val.comp continuous_fst
  have hf : Continuous f := i1_normalTotal_continuous_of_evaluations j k f hb
    (fun W s => i1_normalFrameInverse_evaluation_onOpen_continuous j k U E W s)
  exact hf.subtype_mk (fun p => ((i1_normalFrameEquiv j k U E).symm p).2)

/-- The actual conormal frame gives a local product homeomorphism for the fixed normal topology.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, analytification of local normal frames. -/
def i1_normalFrameHomeomorph (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k)) :
    {v : TotalSpace (Fin k → ℂ) (i1_normalFibre j) | v.proj ∈ Point.overOpen U} ≃ₜ
      ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ) where
  toEquiv := i1_normalFrameEquiv j k U E
  continuous_toFun := i1_normalFrameEquiv_continuous j k U E
  continuous_invFun := i1_normalFrameEquiv_symm_continuous j k U E

end HodgeLean.Foundations.BundleThom

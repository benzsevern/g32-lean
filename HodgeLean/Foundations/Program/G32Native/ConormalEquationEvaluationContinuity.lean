import HodgeLean.Foundations.Program.G32Native.ConormalEquationSectionValue
import HodgeLean.Foundations.Program.G32Native.NormalLocalEvaluationContinuity

/-! # Continuity of evaluation on actual ambient equations -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Evaluation on an original ambient equation is continuous on its actual
normal total-space domain. -/
theorem continuous_normalEquationEvaluation {Q W : Over (Spec ↧ℂ)}
    (i : Q ⟶ W) (k : ℕ) (U : W.left.Opens)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) :
    letI := normalEvaluationTopology (Conormal.sheaf i.left) k
    Continuous (fun z : {v : Bundle.TotalSpace (Fin k → ℂ)
      (normalFibreOfModule (Conormal.sheaf i.left)) | Point.map i v.proj ∈ Point.overOpen U} =>
        z.1.2 (conormalLocalClass i U s z.1.proj z.2)) := by
  letI := normalEvaluationTopology (Conormal.sheaf i.left) k
  let V := i.left ⁻¹ᵁ U
  let f : {v : Bundle.TotalSpace (Fin k → ℂ) (normalFibreOfModule (Conormal.sheaf i.left)) |
      Point.map i v.proj ∈ Point.overOpen U} →
      {v : Bundle.TotalSpace (Fin k → ℂ) (normalFibreOfModule (Conormal.sheaf i.left)) |
        v.proj ∈ Point.overOpen V} :=
    fun z => ⟨z.1, (Point.mem_overOpen_map_iff i z.1.proj U).mp z.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hv := continuous_normalLocalEvaluation (Conormal.sheaf i.left) k V (conormalEquationSection i U s)
  apply (hv.comp hf).congr
  intro z
  exact congrArg z.1.2 (moduleSectionValue_conormalEquationSection i U s z.1.proj z.2)

#print axioms continuous_normalEquationEvaluation

end HodgeLean.Foundations.Program.G32Native

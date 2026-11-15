import HodgeLean.Foundations.Program.G32Native.EulerModel.GlobalNormalSection
import Mathlib.Topology.Constructions

/-! # Continuity of the descended projective kernel section -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators ComplexConjugate
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The standard quotient topology on the projective normal-model base. -/
instance normalProjectiveTopology (k : ℕ) :
    TopologicalSpace (Projectivization ℂ (ℂ × (Fin k → ℂ))) :=
  instTopologicalSpaceQuotient

/-- The global projected vector is continuous in the projective line. -/
theorem continuous_projectiveNormalSectionVector (k : ℕ) :
    Continuous (projectiveNormalSectionVector k) := by
  apply continuous_coinduced_dom.mpr
  change Continuous (fun v : {v : ℂ × (Fin k → ℂ) // v ≠ 0} => homogeneousNormalSection k v.1)
  have hlen : Continuous
      (fun v : {v : ℂ × (Fin k → ℂ) // v ≠ 0} => normalLengthSq k v.1) := by
    unfold normalLengthSq
    fun_prop
  have hn (v : {v : ℂ × (Fin k → ℂ) // v ≠ 0}) : (normalLengthSq k v.1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (normalLengthSq_pos k v.1 v.2))
  have hscalar : Continuous
      (fun v : {v : ℂ × (Fin k → ℂ) // v ≠ 0} => v.1.1 / (normalLengthSq k v.1 : ℂ)) :=
    (continuous_fst.comp continuous_subtype_val).div (Complex.continuous_ofReal.comp hlen) hn
  have hconj : Continuous (fun v : {v : ℂ × (Fin k → ℂ) // v ≠ 0} =>
      (conj v.1.1, fun i => conj (v.1.2 i))) := by
    fun_prop
  exact continuous_const.sub (hscalar.smul hconj)

#print axioms continuous_projectiveNormalSectionVector
/-- The actual kernel family as a subspace of base times the ambient vector space. -/
abbrev ProjectiveNormalTotalSpace (k : ℕ) :=
  {pv : Projectivization ℂ (ℂ × (Fin k → ℂ)) × (ℂ × (Fin k → ℂ)) //
    pv.2 ∈ projectiveNormalKernel k pv.1}

/-- The global section retaining its base point and its actual kernel vector. -/
def projectiveNormalSectionMap (k : ℕ) :
    Projectivization ℂ (ℂ × (Fin k → ℂ)) → ProjectiveNormalTotalSpace k :=
  fun p => ⟨(p, projectiveNormalSectionVector k p), projectiveNormalSectionVector_mem k p⟩

/-- The global section is continuous into the total space of the actual kernel family. -/
theorem continuous_projectiveNormalSectionMap (k : ℕ) :
    Continuous (projectiveNormalSectionMap k) := by
  exact (continuous_id.prodMk (continuous_projectiveNormalSectionVector k)).subtype_mk _

#print axioms continuous_projectiveNormalSectionMap
end HodgeLean.Foundations.Program.G32Native.EulerModel

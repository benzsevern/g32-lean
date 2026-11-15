import HodgeLean.Foundations.Program.G32Native.PairedConormalCechVertices

/-! # Vertex sections retain every original degree-zero cochain -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native
variable {R : Type*} [CommRing R] {X : Scheme} {f : X ⟶ Spec (.of R)}
    (F : OModulePresheaf f) (K : X.OrderedAffineCover)

/-- Equality of the original vertex sections determines the entire cochain. -/
theorem conormalCechVertexSection_injective :
    Function.Injective (conormalCechVertexSection F K) := by
  intro c d h
  funext s
  have hs : s = conormalCechVertex K (s.val 0) := by
    apply Subtype.ext
    funext i
    fin_cases i
    rfl
  rw [hs]
  have hv := congrFun h (s.val 0)
  have hi : K.inter (conormalCechVertex K (s.val 0)) ≤ K.U (s.val 0) :=
    (conormalCechVertex_inter K _).le
  have h' := congrArg (F.res hi) hv
  simp only [conormalCechVertexSection, OModulePresheaf.res_res,
    OModulePresheaf.res_refl_apply] at h'
  exact h'

end HodgeLean.Foundations.Program.G32Native

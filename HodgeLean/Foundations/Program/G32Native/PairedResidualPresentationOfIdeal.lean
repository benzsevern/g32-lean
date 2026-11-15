import HodgeLean.Foundations.Program.G32Native.PairedResidualPresentationDefs
import HodgeLean.Foundations.Program.G32Native.PairedResidualDiagramGeometry
import HodgeLean.Foundations.Program.G32Native.PairedResidualFreeRestriction

/-! # Assembling a residual presentation from its specified ideal -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The canonical union and intersection supply the diagram fields of a residual presentation. -/
def residualPresentationOfIdeal
    {P V : Over (Spec ↧ℂ)} (i : P ⟶ V) [IsClosedImmersion i.left]
    (k : ℕ) (L : P.left.Modules) (J : V.left.IdealSheafData)
    [Smooth (residualComponent (V := V) J).hom]
    (hnot : ¬ (i.left.ker.support : Set V.left) ⊆ J.support)
    (sourceIso : (Scheme.Modules.pullback (residualUnionFirst i J).left).obj
      (s2c_conormal (residualUnionι i J).left) ≅
        (SheafOfModules.free (R := P.left.ringCatSheaf) (Fin k) : P.left.Modules))
    (lastIso : (Scheme.Modules.pushforward (residualIntersectionFirst i J).left).obj
      (s2c_conormal (residualIntersectionSecond i J).left) ≅ L)
    (hframes : ∀ x : P.left, ∃ U : P.left.Opens, x ∈ U ∧
      Nonempty (Scheme.Modules.restrict (s2c_conormal i.left) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules))) :
    PairedResidualPresentation P V i k L where
  T := residualUnion i J
  T₂ := residualComponent (V := V) J
  S := residualIntersection i J
  t := residualUnionι i J
  t₂ := residualComponentι (V := V) J
  a := residualUnionFirst i J
  s₁ := residualIntersectionFirst i J
  s₂ := residualIntersectionSecond i J
  closed_t := inferInstance
  closed_t₂ := inferInstance
  closed_a := inferInstance
  closed_s₁ := inferInstance
  closed_s₂ := inferInstance
  smooth_T₂ := inferInstance
  ha := residualUnionFirst_fac i J
  hs := residualIntersection_square i J
  union_ideal := residualUnion_kernel i J
  intersection_ideal := residualIntersection_kernel i J
  noncontainment := (residual_noncontainment_iff i J).mpr hnot
  sourceIso := sourceIso
  lastIso := lastIso
  local_frames := by
    intro x
    obtain ⟨U, hx, hU⟩ := hframes x
    exact ⟨U, hx, ⟨residual_restrict_free_iso _ k sourceIso U⟩, hU⟩

#print axioms residualPresentationOfIdeal

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.BundleThom.InverseFrameContinuityHelpers

/-! # Trivializations from actual algebraic normal frames

The chart acts on the actual dual conormal total space and uses the fixed topology.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle
namespace HodgeLean.Foundations.BundleThom

variable {Q : Over (Spec ↧ℂ)} {Z : Scheme} (j : Q.left ⟶ Z) (k : ℕ)
private local instance : TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Partial normal coordinates associated to the supplied actual local conormal frame.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, local normal bundle charts. -/
def i1_normalFrameChartPartialEquiv (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k)) :
    PartialEquiv (TotalSpace (Fin k → ℂ) (i1_normalFibre j))
      (ComplexPoint Q × (Fin k → ℂ)) := by
  classical
  let H := i1_normalFrameHomeomorph j k U E
  exact {
    toFun := fun z => (z.proj, if hz : z.proj ∈ Point.overOpen U then (H ⟨z, hz⟩).2 else 0)
    invFun := fun p => if hp : p.1 ∈ Point.overOpen U
      then (H.symm (⟨p.1, hp⟩, p.2)).1 else ⟨p.1, 0⟩
    source := {z | z.proj ∈ Point.overOpen U}
    target := Point.overOpen U ×ˢ Set.univ
    map_source' := by
      intro z hz
      exact ⟨hz, trivial⟩
    map_target' := by
      intro p hp
      simp only [dite_eq_left hp.1]
      exact hp.1
    left_inv' := by
      intro z hz
      change z.proj ∈ Point.overOpen U at hz
      erw [dite_eq_left hz, dite_eq_left hz]
      exact congrArg Subtype.val (H.symm_apply_apply ⟨z, hz⟩)
    right_inv' := by
      intro p hp
      erw [dite_eq_left hp.1]
      have hsource : (H.symm (⟨p.1, hp.1⟩, p.2)).1.proj ∈ Point.overOpen U :=
        (H.symm (⟨p.1, hp.1⟩, p.2)).2
      erw [dite_eq_left hsource]
      exact congrArg (fun q : ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ) =>
        (q.1.1, q.2)) (H.apply_symm_apply (⟨p.1, hp.1⟩, p.2)) }

/-- The actual local normal frame defines a trivialization for the prescribed total topology.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8; Bott–Tu, §6, local bundle charts. -/
def i1_normalFrameTrivialization (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k)) :
    Trivialization (Fin k → ℂ)
      (TotalSpace.proj : TotalSpace (Fin k → ℂ) (i1_normalFibre j) → ComplexPoint Q) := by
  classical
  let e := i1_normalFrameChartPartialEquiv j k U E
  let H := i1_normalFrameHomeomorph j k U E
  refine {
    toOpenPartialHomeomorph := {
      toPartialEquiv := e
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_
      open_source := (Point.isOpen_overOpen U).preimage (i1_normalProjection_continuous j k)
      open_target := (Point.isOpen_overOpen U).prod isOpen_univ }
    baseSet := Point.overOpen U
    open_baseSet := Point.isOpen_overOpen U
    source_eq := rfl
    target_eq := rfl
    proj_toFun := by intro p hp; rfl }
  · apply continuousOn_iff_continuous_restrict.mpr
    change Continuous (fun z : {v : TotalSpace (Fin k → ℂ) (i1_normalFibre j) |
      v.proj ∈ Point.overOpen U} => e z.1)
    have ho : Continuous (fun p : ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ) =>
        (p.1.1, p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact (ho.comp H.continuous).congr (fun z => by
      change (z.1.proj, (H z).2) =
        (z.1.proj, if hz : z.1.proj ∈ Point.overOpen U then (H ⟨z.1, hz⟩).2 else 0)
      have hz : z.1.proj ∈ Point.overOpen U := z.2
      erw [dite_eq_left hz])
  · apply continuousOn_iff_continuous_restrict.mpr
    change Continuous (fun p : ↥(Point.overOpen U ×ˢ (Set.univ : Set (Fin k → ℂ))) => e.symm p.1)
    have hb : Continuous (fun p : ↥(Point.overOpen U ×ˢ (Set.univ : Set (Fin k → ℂ))) => p.1.1) :=
      continuous_fst.comp continuous_subtype_val
    have hbu : Continuous (fun p : ↥(Point.overOpen U ×ˢ (Set.univ : Set (Fin k → ℂ))) =>
        (⟨p.1.1, p.2.1⟩ : ↥(Point.overOpen U : Set (ComplexPoint Q)))) :=
      hb.subtype_mk (fun p => p.2.1)
    have hv : Continuous (fun p : ↥(Point.overOpen U ×ˢ (Set.univ : Set (Fin k → ℂ))) => p.1.2) :=
      continuous_snd.comp continuous_subtype_val
    have hc := continuous_subtype_val.comp (H.symm.continuous.comp (hbu.prodMk hv))
    exact hc.congr (fun p => by
      change (H.symm (⟨p.1.1, p.2.1⟩, p.1.2)).1 =
        (if hp : p.1.1 ∈ Point.overOpen U then (H.symm (⟨p.1.1, hp⟩, p.1.2)).1 else ⟨p.1.1, 0⟩)
      erw [dite_eq_left p.2.1])

/-- Each actual normal-frame trivialization is complex linear on every fibre over its base set.
Source: Hartshorne, Algebraic Geometry, II.8; Bott–Tu, §6, complex linear bundle charts. -/
theorem i1_normalFrameTrivialization_isLinear (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k)) :
    (i1_normalFrameTrivialization j k U E).IsLinear ℂ := by
  classical
  constructor
  intro b hb
  have hb' : b ∈ Point.overOpen U := hb
  let L : i1_normalFibre j b ≃ₗ[ℂ] (Fin k → ℂ) :=
    (i1_conormalFrameBasis j k U E b hb').dualBasis.equivFun
  have he : (fun v : i1_normalFibre j b =>
      (i1_normalFrameTrivialization j k U E (⟨b, v⟩ : TotalSpace (Fin k → ℂ) (i1_normalFibre j))).2) =
      (fun v => L v) := by
    funext v
    change (if hx : b ∈ Point.overOpen U then
      (i1_normalFrameHomeomorph j k U E ⟨⟨b, v⟩, hx⟩).2 else 0) = L v
    erw [dite_eq_left hb']
    rfl
  exact he.symm ▸ L.toLinearMap.isLinear

end HodgeLean.Foundations.BundleThom

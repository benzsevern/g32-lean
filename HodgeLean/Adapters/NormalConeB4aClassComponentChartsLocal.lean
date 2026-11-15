import HodgeLean.Adapters.NormalConeB4aClassSourceOpenCharts
import HodgeLean.Adapters.NormalConeB4aClassSmoothComponentLocal

/-! # Normal charts without constant ambient dimension

Route: choose a standard-smooth affine ambient neighborhood, restrict the
component immersion to it, and compute the smooth source dimension using
the component's closed point. Transport the resulting chart to the ambient.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Regular component points have holomorphic normal charts of the expected
codimension even when the ambient smooth scheme has varying dimension. -/
theorem a3b4a_classComponent_exists_holomorphic_flattening_local
    (X : Over (Spec (CommRingCat.of ℂ))) (c : ℕ)
    [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (ξ : X.left) (hc : Order.coheight ξ = c)
    (y : ComplexPoint X) (hy : y.underlying ∈ closure ({ξ} : Set X.left))
    (hreg : y.underlying ∉ reducedClosedSingularRemainder X.hom
      ⟨closure {ξ}, isClosed_closure⟩) :
    ∃ r : ℕ, ∃ e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)),
      y ∈ e.source ∧ a3b4_IsHolChart X.hom e ∧
      ∀ x ∈ e.source, x.underlying ∈ closure ({ξ} : Set X.left) ↔ (e x).2 = 0 := by
  let C := Over.mk (cycleComponentι X.left ξ ≫ X.hom)
  let k : C ⟶ X := Over.homMk (cycleComponentι X.left ξ) rfl
  letI : LocallyOfFiniteType C.hom := inferInstanceAs
    (LocallyOfFiniteType (cycleComponentι X.left ξ ≫ X.hom))
  letI : IsClosedImmersion k.left := inferInstanceAs (IsClosedImmersion (cycleComponentι X.left ξ))
  have hyr : y ∈ Set.range (Point.map k) := by
    rw [ComplexPoint.range_map_of_isImmersion_of_comm X C k]
    change y.underlying ∈ Set.range (cycleComponentι X.left ξ)
    rwa [range_cycleComponentι]
  obtain ⟨z, rfl⟩ := hyr
  let A := (cycleComponentι X.left ξ ≫ X.hom).smoothLocus
  have hzA : z.underlying ∈ A := by
    by_contra hz
    exact hreg ⟨z.underlying, hz, rfl⟩
  have hzClosed : IsClosed {z.underlying} :=
    ((pointEquivClosedPoint C.hom) ⟨z.left, Over.w z⟩).2
  obtain ⟨U, hU, hyU, hs⟩ := Smooth.exists_affine_isStandardSmooth X.hom (Point.map k z).underlying
  obtain ⟨d, hd⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension hs
  let XU := ComplexPoint.openScheme X U
  let W := k.left ⁻¹ᵁ U
  let CW := ComplexPoint.openScheme C W
  let A' := W.ι ⁻¹ᵁ A
  let i : CW ⟶ XU := Over.homMk (k.left ∣_ U) (by
    change (k.left ∣_ U) ≫ (U.ι ≫ X.hom) = W.ι ≫ C.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, k.w])
  letI : IsAffine U.toScheme := hU
  letI : IsAffine XU.left := hU
  letI : SmoothOfRelativeDimension d XU.hom :=
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth X.hom hU hd
  letI : Smooth XU.hom := SmoothOfRelativeDimension.smooth d XU.hom
  letI : LocallyOfFiniteType XU.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  letI : QuasiCompact XU.hom := (quasiCompact_iff_compactSpace XU.hom).2 inferInstance
  letI : IsSeparated XU.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
  letI : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (k.left ∣_ U))
  letI : SmoothOfRelativeDimension (d-c) (A.ι ≫ C.hom) :=
    a3b4a_classComponent_smoothLocus_relativeDimension_local X ξ hc z.underlying
      hzA hzClosed U hU hyU hd
  letI : SmoothOfRelativeDimension (d-c) (ComplexPoint.openScheme CW A').hom := by
    change SmoothOfRelativeDimension (d-c) (A'.ι ≫ W.ι ≫ C.hom)
    rw [← Category.assoc, ← morphismRestrict_ι W.ι A, Category.assoc]
    simpa only [Nat.zero_add] using
      smoothOfRelativeDimension_comp 0 (d-c) (W.ι ∣_ A) (A.ι ≫ C.hom)
  let zW := ComplexPoint.asOpenPoint C W z hyU
  have hzWmap : Point.map (ComplexPoint.openInclusion C W) zW = z :=
    Over.OverMorphism.ext (ComplexPoint.liftToOpen_fac C W z hyU)
  have hzWA : zW.underlying ∈ A' := by
    change W.ι zW.underlying ∈ A
    have hh := congrArg Point.underlying hzWmap
    change W.ι zW.underlying = z.underlying at hh
    rwa [hh]
  let zA := ComplexPoint.asOpenPoint CW A' zW hzWA
  have hξU : ξ ∈ U := (specializes_iff_mem_closure.mpr hy).mem_open U.isOpen hyU
  have hcd : c ≤ d := by
    have h := SmoothOfRelativeDimension.coheight_le_complex (f := XU.hom) (d := d)
      (⟨ξ, hξU⟩ : U.toScheme)
    have he := coheight_eq_of_isOpenImmersion (x := (⟨ξ, hξU⟩ : U.toScheme)) U.ι
    change Order.coheight ξ = _ at he
    rw [← he, hc] at h
    exact_mod_cast h
  have hdc : d - (d-c) = c := by omega
  have hex := a3b4a_classSourceOpen_exists_holomorphic_flattening XU CW i (d-c) d A' zA
  rw [hdc] at hex
  obtain ⟨e, hze, he, hflat⟩ := hex
  letI : Nonempty (ComplexPoint XU) := ⟨Point.map (ComplexPoint.openInclusion CW A' ≫ i) zA⟩
  obtain ⟨E, hE, hsource, heval⟩ :=
    a3b4a_classHolomorphicChart_openTransport X U (d-c) c e he
  let f := Point.map (ComplexPoint.openInclusion X U)
  have hpoint : f (Point.map (ComplexPoint.openInclusion CW A' ≫ i) zA) = Point.map k z := by
    apply Over.OverMorphism.ext
    change (zA.left ≫ (A'.ι ≫ (k.left ∣_ U))) ≫ U.ι = z.left ≫ k.left
    rw [Category.assoc, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, ← Category.assoc]
    have h₁ : zA.left ≫ A'.ι = zW.left := ComplexPoint.liftToOpen_fac CW A' zW hzWA
    have h₂ : zW.left ≫ W.ι = z.left := ComplexPoint.liftToOpen_fac C W z hyU
    rw [h₁, h₂]
  have hrange : Set.range (k.left ∣_ U) = U.ι ⁻¹' Set.range k.left := by
    ext u
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.1, (morphismRestrict_base_coe k.left U w).symm⟩
    · rintro ⟨w, hw⟩
      have hwU : w ∈ W := by
        change k.left w ∈ U
        rw [hw]
        exact u.2
      refine ⟨⟨w, hwU⟩, Subtype.ext ?_⟩
      exact (morphismRestrict_base_coe k.left U ⟨w, hwU⟩).trans hw
  have hS : f ⁻¹' (Point.underlying ⁻¹' closure ({ξ} : Set X.left)) =
      Set.range (Point.map i) := by
    rw [ComplexPoint.range_map_of_isImmersion_of_comm XU CW i]
    change _ = (Point.underlying : ComplexPoint XU → XU.left) ⁻¹' Set.range (k.left ∣_ U)
    rw [hrange]
    change _ = (Point.underlying : ComplexPoint XU → U.toScheme) ⁻¹'
      ((fun u : U.toScheme => U.ι u) ⁻¹' Set.range (cycleComponentι X.left ξ))
    rw [range_cycleComponentι]
    rfl
  refine ⟨d-c, E, ?_, hE, ?_⟩
  · rw [hsource, ← hpoint]
    exact ⟨_, hze, rfl⟩
  · intro x hx
    rw [hsource] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [heval]
    change w ∈ f ⁻¹' (Point.underlying ⁻¹' closure ({ξ} : Set X.left)) ↔ _
    rw [hS]
    exact hflat w hw

end HodgeLean.Adapters

import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Defs
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Topology.JacobsonSpace

/-! # Local detection of radical scheme ideals

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

/-- Radical ideals on an affine neighborhood of every point determine a radical ideal sheaf.
Source: Hartshorne, Algebraic Geometry, II.5, local properties of ideal sheaves.
HC no distance; AV milestone no distance.
-/
theorem radical_of_affine_neighborhoods (X : Scheme) (I : X.IdealSheafData)
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ (I.ideal U).IsRadical) :
    I.radical = I := by
  choose U hmem hrad using h
  have hcover : ⨆ x, (U x).1 = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hmem x⟩
  apply le_antisymm
  · apply Scheme.IdealSheafData.le_of_iSup_eq_top U hcover
    intro x
    exact (hrad x).radical.le
  · exact I.le_radical

/-- Radicality of the ideal on an affine open subscheme identifies radicality in the original section ring.
Source: Hartshorne, Algebraic Geometry, II.5; affine open section isomorphism.
HC no distance; AV milestone no distance.
-/
theorem radical_of_affine_open_comap (X : Scheme) (I : X.IdealSheafData)
    (U : X.Opens) (hU : IsAffineOpen U)
    (h : letI : IsAffine U.toScheme := hU
      ((I.comap U.ι).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩).IsRadical) :
    (I.ideal ⟨U, hU⟩).IsRadical := by
  letI : IsAffine U.toScheme := hU
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h
  let J := I.ideal ⟨U.ι ''ᵁ ⊤, (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩
  let φ := (U.ι.appIso ⊤).inv.hom
  have hsurj : Function.Surjective φ := (U.ι.appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective
  have hrad : J.radical.comap φ = J.comap φ := by
    rw [Ideal.comap_radical]
    exact h.radical
  have hJ : J.IsRadical := Ideal.radical_eq_iff.mp
    (Ideal.comap_injective_of_surjective φ hsurj hrad)
  have hEq : (⟨U.ι ''ᵁ ⊤, (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩ :
      X.affineOpens) = ⟨U, hU⟩ := Subtype.ext (Scheme.Opens.ι_image_top U)
  change (I.ideal ⟨U.ι ''ᵁ ⊤, (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩).IsRadical at hJ
  rw [hEq] at hJ
  exact hJ

/-- It suffices to detect radical section ideals on affine neighborhoods of complex points.
Source: Hartshorne, Algebraic Geometry, II.3 and II.5, Jacobson detection.
HC no distance; AV milestone no distance.
-/
theorem radical_of_complex_neighborhoods (B : Over (Spec ↧ℂ)) [LocallyOfFiniteType B.hom]
    (I : B.left.IdealSheafData)
    (h : ∀ x : ComplexPoint B, ∃ U : B.left.affineOpens,
      x.underlying ∈ U.1 ∧ (I.ideal U).IsRadical) : I.radical = I := by
  letI : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  apply radical_of_affine_neighborhoods B.left I
  intro y
  obtain ⟨p, hp, hc⟩ := nonempty_inter_closedPoints
    (Z := closure ({y} : Set B.left)) ⟨y, subset_closure (Set.mem_singleton y)⟩
    isClosed_closure.isLocallyClosed
  let xp : ComplexPoint B := Over.homMk (pointOfClosedPoint B.hom p hc) (by simp)
  have hxp : xp.underlying = p := pointOfClosedPoint_apply B.hom p hc _
  obtain ⟨U, hU, hr⟩ := h xp
  refine ⟨U, ?_, hr⟩
  have hsp : y ⤳ p := specializes_iff_mem_closure.mpr hp
  apply hsp.mem_open U.1.isOpen
  rw [hxp] at hU
  exact hU

/-- Away from the support, an affine neighborhood has the unit ideal after restriction.
Source: Hartshorne, Algebraic Geometry, II.5, support of a quotient sheaf.
HC no distance; AV milestone no distance.
-/
theorem radical_neighborhood_off_support (X : Scheme) (I : X.IdealSheafData)
    (x : X) (hx : x ∉ I.support) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ (I.ideal U).IsRadical := by
  let V : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ V from hx)
  letI : IsAffine U.toScheme := hU
  have htop : I.comap U.ι = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff (I := I.comap U.ι)).mp
    apply TopologicalSpace.Closeds.ext
    ext y
    constructor
    · intro hy
      rw [Scheme.IdealSheafData.support_comap] at hy
      exact hUV y.property hy
    · intro hy
      exact False.elim hy
  refine ⟨⟨U, hU⟩, hxU, radical_of_affine_open_comap X I U hU ?_⟩
  rw [htop]
  exact Ideal.radical_eq_iff.mp (Ideal.radical_top _)

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo

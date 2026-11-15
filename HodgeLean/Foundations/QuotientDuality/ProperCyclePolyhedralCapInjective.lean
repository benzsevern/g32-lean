import HodgeLean.Foundations.QuotientDuality.ProperCycleMaximalFaceNormalChart
import HodgeLean.Foundations.QuotientDuality.ProperCyclePolyhedralSheafPurity
import HodgeLean.Foundations.QuotientDuality.ProperCycleGlobalBoundaryGermDetection
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartRestrictionDetection
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenPolyhedralPurity
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceSubcomplex

/-! # Actual supported cap injectivity on finite geometric subcomplex supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The original collar support cap is injective for a finite geometric support of bounded dimension, with the specified ambient point orientation lines and concentration.
Source: properCycle_maximal_face_full_support_normal_chart; ProperCycleSupportCollar.chart_restriction_zero_of_cap_point_zero; properCycle_global_zero_of_off_boundary_local_restrictions; properCycle_finite_skeleton_open_relative_vanishes.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_subcomplex_support_cap_injective {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces) (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (hS : IsClosed {z : K.space | z.val ∈ D.space})
    (C : ProperCycleSupportCollar (TopCat.of K.space) {z : K.space | z.val ∈ D.space})
    (p q : ℕ) (hp : Even p) (hdim : ∀ s ∈ D.faces, s.card ≤ q + 1)
    (c : Homology ℚ (TopCat.of K.space) (p+q))
    (hlocal : ∀ x, Function.Bijective (orientationLine (TopCat.of K.space) (p+q) c x))
    (hvan : ∀ j : ℕ, j ≠ p+q → ∀ x : K.space,
      Subsingleton (orientationGroup (TopCat.of K.space) j x)) :
    Function.Injective (C.cap hS p q c) := by
  classical
  let X := TopCat.of K.space
  letI : ∀ U : Opens K.space, ParacompactSpace U := fun _ => inferInstance
  have hD : D.faces.Finite := hK.subset hDK
  let S : Closeds X := ⟨{z : K.space | z.val ∈ D.space}, hS⟩
  let B := properCycle_subcomplex_skeleton_filtration K D hD q
  have hBS : B ≤ S := by
    rintro z ⟨s, hs, _, hzs⟩
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, hs, hzs⟩
  have hboundary : IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set X) B) p) :=
    properCycle_finite_skeleton_open_relative_vanishes K D hK hDK V hV ⊤ (p+q)
      (fun j hj x _ => hvan j hj x) q p (by omega)
  have hlow (j : ℕ) (hj : j < p) : IsZero (supportRelativeCohomologySheaf X S j) :=
    properCycle_finite_subcomplex_support_sheaf_vanishes K D hK hDK V hV (p+q) hvan
      (q+1) hdim j (by omega)
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro a ha
  apply properCycle_global_zero_of_off_boundary_local_restrictions X S B hBS p hboundary hlow a
  intro x hxS hxB
  obtain ⟨s, hs, hxs⟩ := s2v_hardt6rb_mem_open_face D hxS
  have hncard : ¬ s.card ≤ q := fun h => hxB ⟨s, hs, h, intrinsicInterior_subset hxs⟩
  have hcard : s.card = q+1 := by have h := hdim s hs; omega
  have hmax (t : Finset E) (ht : t ∈ D.faces) (hst : s ⊆ t) : t = s :=
    (Finset.eq_of_subset_of_card_le hst (by rw [hcard]; exact hdim t ht)).symm
  obtain ⟨j, Y, y, b, hY, htarget, hxb, hcenter, hdimension, hflat⟩ :=
    properCycle_maximal_face_full_support_normal_chart K D hK hDK V hV s hs hmax x hxs
  have hq : Module.finrank ℝ (properCycle_log_tangent j) = q := by omega
  subst q
  letI : ContractibleSpace Y := hY
  let H : b.source ≃ₜ (properCycle_log_tangent j × Y) := b.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr htarget).trans (Homeomorph.Set.univ _))
  letI : T1Space (properCycle_log_tangent j × Y) := H.t1Space
  letI : T1Space Y := t1Space_of_injective_of_continuous
    (f := fun y : Y => ((0 : properCycle_log_tangent j), y))
    (fun u v h => congrArg Prod.snd h) (continuous_const.prodMk continuous_id)
  have hzero : localOrientation (TopCat.of (S : Set X))
      (Module.finrank ℝ (properCycle_log_tangent j))
      (C.cap hS p (Module.finrank ℝ (properCycle_log_tangent j)) c a) ⟨x, hxS⟩ = 0 := by
    rw [ha]
    exact map_zero _
  have hrestriction := C.chart_restriction_zero_of_cap_point_zero hS (properCycle_log_tangent j)
    Y b htarget y hflat ⟨x, hxS⟩ hxb hcenter p hp a c (hlocal x) hzero
  exact ⟨⟨b.source, b.open_source⟩, hxb, hrestriction⟩

end HodgeLean.Foundations.QuotientDuality

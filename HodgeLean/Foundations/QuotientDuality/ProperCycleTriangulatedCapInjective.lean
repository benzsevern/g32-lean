import HodgeLean.Foundations.QuotientDuality.ProperCyclePolyhedralCapInjective
import HodgeLean.Foundations.QuotientDuality.ProperCycleHomeomorphCapInjective
import HodgeLean.Foundations.QuotientDuality.ProperCycleHomeomorphOrientationLine
import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTransport

/-! # Original support cap injectivity in actual marked triangulated spaces
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual marked finite triangulation transfers original support-cap injectivity with its specified ambient fundamental class and point-line data.
Source: properCycle_finite_subcomplex_support_cap_injective; properCycle_support_cap_injective_of_comapHomeomorph; properCycle_homeomorph_orientation_line_bijective.
HC no distance; AV milestone no distance. -/
lemma properCycle_triangulated_support_cap_injective {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (X : TopCat.{0}) [T1Space X] (S : Set X) (hS : IsClosed S)
    (C : ProperCycleSupportCollar X S)
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces) (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (e : K.space ≃ₜ X) (hmark : ∀ z : K.space, e z ∈ S ↔ z.val ∈ D.space)
    (p q : ℕ) (hp : Even p) (hdim : ∀ s ∈ D.faces, s.card ≤ q+1)
    (c : Homology ℚ X (p+q))
    (hlocal : ∀ x, Function.Bijective (orientationLine X (p+q) c x))
    (hvan : ∀ j : ℕ, j ≠ p+q → ∀ x : X, Subsingleton (orientationGroup X j x)) :
    Function.Injective (C.cap hS p q c) := by
  let Y := TopCat.of K.space
  let T : Set Y := {z : K.space | z.val ∈ D.space}
  have he : ∀ z : Y, z ∈ T ↔ e z ∈ S := fun z => (hmark z).symm
  have hT : IsClosed T := by
    have ht : T = e ⁻¹' S := Set.ext he
    rw [ht]
    exact hS.preimage e.continuous
  let f : Y ⟶ X := TopCat.ofHom ⟨e, e.continuous⟩
  let fi : X ⟶ Y := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  let cY := homologyMap ℚ (p+q) fi c
  have hpush : homologyMap ℚ (p+q) f cY = c := by
    have hfi : fi ≫ f = 𝟙 X := by ext x : 1; exact e.apply_symm_apply x
    change ((homologyMap ℚ (p+q) f).comp (homologyMap ℚ (p+q) fi)) c = c
    rw [← homologyMap_comp, hfi, homologyMap_id, LinearMap.id_apply]
  have hlocalY (z : Y) : Function.Bijective (orientationLine Y (p+q) cY z) := by
    have h := properCycle_homeomorph_orientation_line_bijective X Y e.symm (p+q) c (e z) (hlocal (e z))
    exact (e.symm_apply_apply z) ▸ h
  have hvanY (j : ℕ) (hj : j ≠ p+q) (z : Y) : Subsingleton (orientationGroup Y j z) := by
    let H := properCycle_local_homology_homeomorph_iso (X := Y) (Y := X) e z j
    exact @Function.Injective.subsingleton _ _ H.toLinearEquiv H.toLinearEquiv.injective (hvan j hj (e z))
  let D0 : ProperCycleSupportCollar Y T := C.comapHomeomorph (X := Y) (Y := X) (S := T) (T := S) e he
  have hinj := properCycle_finite_subcomplex_support_cap_injective K D hK hDK V hV hT
    D0 p q hp hdim cY hlocalY hvanY
  have h := properCycle_support_cap_injective_of_comapHomeomorph (X := Y) (Y := X) (S := T) (T := S) C e he hT hS p q cY hinj
  exact hpush ▸ h

end HodgeLean.Foundations.QuotientDuality

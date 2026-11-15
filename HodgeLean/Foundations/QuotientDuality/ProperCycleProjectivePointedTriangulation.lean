import HodgeLean.Foundations.QuotientDuality.ProperCycleSingletonSubcomplexVertex
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexPointClosedMap

/-! # Actual projective boundary triangulations retaining a specified outside point -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

/-- An original closed projective support and an original point outside it have a common full finite triangulation in which that very point is a vertex outside the support subcomplex.
Source: properCycle_projective_full_triangulation; properCycle_complex_point_map_range; properCycle_singleton_subcomplex_vertex.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_pointed_full_triangulation
    (X Z : Over (Spec ↧ℂ)) [IsProjective X.hom] (i : Z ⟶ X)
    [IsClosedImmersion i.left] (x : ComplexPoint X) (hx : x ∉ Set.range (Point.map i)) :
    ∃ a : ℕ, ∃ K D : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)),
      K.faces.Finite ∧ D.faces ⊆ K.faces ∧
        (∀ s ∈ K.faces, (∀ y ∈ s, y ∈ D.vertices) → s ∈ D.faces) ∧
        ∃ h : K.space ≃ₜ ComplexPoint X,
          (∀ y : K.space, h y ∈ Set.range (Point.map i) ↔ y.val ∈ D.space) ∧
          ({(h.symm x).val} : Finset _) ∈ K.faces ∧ (h.symm x).val ∉ D.vertices := by
  classical
  let Zs : Fin 2 → Over (Spec ↧ℂ) := ![Z, Over.mk (𝟙 (Spec ↧ℂ))]
  let maps : ∀ j, Zs j ⟶ X := Fin.cases i (Fin.cases x (fun j => Fin.elim0 j))
  letI (j : Fin 2) : IsClosedImmersion (maps j).left := by
    fin_cases j
    · exact inferInstanceAs (IsClosedImmersion i.left)
    · exact properCycle_complex_point_closed_immersion X x
  obtain ⟨a, K, hK, h, hm⟩ := properCycle_projective_full_triangulation X Zs maps
  obtain ⟨D, _, hDK, hfull, hDmark⟩ := hm 0
  change ∀ y : K.space, h y ∈ Set.range (Point.map i) ↔ y.val ∈ D.space at hDmark
  obtain ⟨L, _, hLK, _, hLmark⟩ := hm 1
  change ∀ y : K.space, h y ∈ Set.range (Point.map x) ↔ y.val ∈ L.space at hLmark
  rw [properCycle_complex_point_map_range] at hLmark
  let p := (h.symm x).val
  have hspace : L.space = {p} := by
    ext z
    constructor
    · intro hz
      have hzK : z ∈ K.space := by
        obtain ⟨s, hs, hzs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hz
        exact K.convexHull_subset_space (hLK hs) hzs
      let y : K.space := ⟨z, hzK⟩
      have hy : h y = x := (hLmark y).mpr hz
      have hy' : y = h.symm x := h.injective (hy.trans (h.apply_symm_apply x).symm)
      exact congrArg Subtype.val hy'
    · intro hz
      have hz' : z = p := hz
      rw [hz']
      exact (hLmark (h.symm x)).mp (h.apply_symm_apply x)
  have hp : ({p} : Finset _) ∈ K.faces := properCycle_singleton_subcomplex_vertex K L hLK p hspace
  have hpD : p ∉ D.vertices := by
    intro hv
    have hpDspace : p ∈ D.space := D.convexHull_subset_space hv (by simp)
    have hxS := (hDmark (h.symm x)).mpr hpDspace
    rw [Homeomorph.apply_symm_apply] at hxS
    exact hx hxS
  exact ⟨a, K, D, hK, hDK, hfull, h, hDmark, hp, hpD⟩

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenPolyhedralPurity
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexChartDimension

/-! # Actual subcomplex purity from charted pieces only on the requested open -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Bounds only on open faces meeting the specified open identify its actual subcomplex support with the bounded skeleton there.
Source: Munkres, Elements of Algebraic Topology, section 2, intrinsic open faces and skeleta.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_on_open_eq_skeleton {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K D : Geometry.SimplicialComplex ℝ E) (hD : D.faces.Finite) (m : ℕ) (U : Opens K.space)
    (hfaces : ∀ s ∈ D.faces, ∀ x : K.space, x ∈ U →
      x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) → s.card ≤ m) :
    ∀ z : U, z.val.val ∈ D.space ↔
      (z.val : K.space) ∈ properCycle_subcomplex_skeleton_filtration K D hD m := by
  intro z
  constructor
  · intro hz
    obtain ⟨s, hs, hzs⟩ := s2v_hardt6rb_mem_open_face D hz
    exact ⟨s, hs, hfaces s hs z.val z.property hzs, intrinsicInterior_subset hzs⟩
  · rintro ⟨s, hs, _, hz⟩
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, hs, hz⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Support purity on an actual open needs neither concentration nor face dimension bounds outside that open.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9, support localization.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_subcomplex_open_relative_vanishes {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces) (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (U : Opens K.space) (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : K.space, x ∈ U →
      Subsingleton (orientationGroup (TopCat.of K.space) j x))
    (m n : ℕ) (hbound : n + m ≤ N)
    (hfaces : ∀ s ∈ D.faces, ∀ x : K.space, x ∈ U →
      x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) → s.card ≤ m) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set K.space) {z : K.space | z.val ∈ D.space}) n) := by
  have hD : D.faces.Finite := hK.subset hDK
  let B := properCycle_subcomplex_skeleton_filtration K D hD m
  have hz := properCycle_finite_skeleton_open_relative_vanishes K D hK hDK V hV U N hvan m n hbound
  have hlocal := properCycle_subcomplex_on_open_eq_skeleton K D hD m U hfaces
  let e : neighborhoodSupportComplementPair (U : Set K.space) {z : K.space | z.val ∈ D.space} ≅
      neighborhoodSupportComplementPair (U : Set K.space) (B : Set K.space) :=
    TopPair.isoOfSubset (Homeomorph.refl U) (fun z => not_congr (hlocal z).symm)
  let H := (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
    (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso e.symm))
  exact hz.of_iso H

/-- Actual complex charts on triangulated pieces provide the entire local support-purity dimension input.
Source: Hatcher, Algebraic Topology, section 2.2; Bredon, Sheaf Theory, second edition, V.9,
finite stratification and local dimension.
HC no distance; AV milestone no distance. -/
lemma properCycle_charted_subcomplex_open_relative_vanishes {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces) (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (U : Opens K.space) (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : K.space, x ∈ U →
      Subsingleton (orientationGroup (TopCat.of K.space) j x))
    (d n : ℕ) (hbound : n + (2 * d + 1) ≤ N)
    (hpieces : ∀ s ∈ D.faces, ∀ x : K.space, x ∈ U →
      x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) →
      ∃ (L : Geometry.SimplicialComplex ℝ E), L.faces ⊆ K.faces ∧ s ∈ L.faces ∧
        ∃ (X : TopCat.{0}) (e : L.space ≃ₜ X) (z : L.space), z.val = x.val ∧
          ∃ (m : ℕ) (φ : OpenPartialHomeomorph X (Fin m → ℂ)), m ≤ d ∧ e z ∈ φ.source) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set K.space) {z : K.space | z.val ∈ D.space}) n) := by
  apply properCycle_finite_subcomplex_open_relative_vanishes K D hK hDK V hV U N hvan
    (2 * d + 1) n hbound
  intro s hs x hxU hxs
  obtain ⟨L, hLK, hsL, X, e, z, hzx, m, φ, hm, hφ⟩ := hpieces s hs x hxU hxs
  have hL : L.faces.Finite := hK.subset hLK
  have hLV : ∀ a ∈ L.vertices, a ∈ V := fun a ha => hV a (hLK ha)
  have hzs : z.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := hzx.symm ▸ hxs
  have h := properCycle_face_card_le_of_complex_chart X L hL V hLV e s hsL z hzs m φ hφ
  omega

end HodgeLean.Foundations.QuotientDuality

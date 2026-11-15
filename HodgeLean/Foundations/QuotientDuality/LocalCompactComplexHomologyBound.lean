import HodgeLean.Foundations.QuotientDuality.LocalAffineOpenHomologyBound
import HodgeLean.Foundations.QuotientDuality.LocalFiniteOpenHomologyBound

/-! Compact complex schemes have a uniform bound on open-subset singular homology. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

theorem compact_complex_open_homology_bound (X : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] [CompactSpace (ComplexPoint X)] :
    ∃ N : ℕ, ∀ (Z : TopCat.{0}) (j : Z ⟶ TopCat.of (ComplexPoint X)),
      IsOpenEmbedding j → ∀ i, N < i → Subsingleton (Homology ℚ Z i) := by
  classical
  let U (a : X.left.affineOpens) : Opens (ComplexPoint X) :=
    ⟨Point.overOpen a.1, Point.isOpen_overOpen a.1⟩
  have hcover (x : ComplexPoint X) : ∃ a, x ∈ U a := by
    obtain ⟨a, ha, hx, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := X.left) (x := x.underlying) (U := ⊤) (by trivial)
    exact ⟨⟨a, ha⟩, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun a => (U a : Set (ComplexPoint X)))
    (fun a => (U a).isOpen) (fun x _ => Set.mem_iUnion.mpr (hcover x))
  have hb (a : X.left.affineOpens) : ∃ N : ℕ,
      ∀ (Z : TopCat.{0}) (j : Z ⟶ TopCat.of (U a)), IsOpenEmbedding j →
        ∀ i, N < i → Subsingleton (Homology ℚ Z i) := by
    let A := openScheme X a.1
    letI : IsAffine A.left := a.2
    letI : LocallyOfFiniteType A.hom := inferInstanceAs (LocallyOfFiniteType (a.1.ι ≫ X.hom))
    obtain ⟨N, hN⟩ := affine_complex_open_homology_bound A
    let E : ComplexPoint A ≃ₜ U a := openHomeomorph X a.1
    refine ⟨N, ?_⟩
    intro Z j hj i hi
    exact hN Z (j ≫ TopCat.ofHom ⟨E.symm, E.symm.continuous⟩)
      (E.symm.isOpenEmbedding.comp hj) i hi
  obtain ⟨N, hN⟩ := finite_open_homology_bound (TopCat.of (ComplexPoint X))
    X.left.affineOpens U hb s
  refine ⟨N, ?_⟩
  intro Z j hj i hi
  apply hN Z j hj ?_ i hi
  rintro _ ⟨z, rfl⟩
  have H := hs (Set.mem_univ (j z))
  change j z ∈ (⨆ a ∈ s, U a)
  simp only [Opens.mem_iSup]
  simp only [Set.mem_iUnion] at H
  obtain ⟨a, ha, hx⟩ := H
  exact ⟨a, ha, hx⟩

#print axioms compact_complex_open_homology_bound
end HodgeLean.Foundations.QuotientDuality

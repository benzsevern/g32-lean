import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionLimitHomology
import HodgeLean.Foundations.RationalHomologyManifold.RelativeChainKernel
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Topology.Sheaves.LocallySurjective

/-! Actual finite-stage representatives of sections in the supported subdivision limit.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Every section of the actual presheaf subdivision colimit comes from a finite subdivision stage.
Source: Bredon, Sheaf Theory, second edition, VI.12; the subdivision limit of supported chains.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitPresheaf_section_exists (X : TopCat.{0}) (n : ℕ) (U : Opens X)
    (z : ((subdivisionLimitPresheafComplex X).X n).obj (Opposite.op U)) :
    ∃ (m : ℕ) (y : ((singularChainPresheafComplex ℚ X).X n).obj (Opposite.op U)),
      (((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op U)) y = z := by
  let D := presheafSubdivisionDiagram X
  let E : ChainComplex (TopCat.Presheaf AddCommGrpCat.{0} X) ℕ ⥤ AddCommGrpCat.{0} :=
    HomologicalComplex.eval (TopCat.Presheaf AddCommGrpCat.{0} X) (ComplexShape.down ℕ) n ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (Opposite.op U)
  letI : PreservesColimit D E := by
    dsimp only [D, E, TopCat.Presheaf]
    infer_instance
  let e := preservesColimitIso E D
  obtain ⟨m, y, hy⟩ := Concrete.colimit_exists_rep (D ⋙ E) (e.hom z)
  refine ⟨m, y, ?_⟩
  have h := ConcreteCategory.congr_hom (ι_preservesColimitIso_inv E D m) y
  simp only [ConcreteCategory.comp_apply] at h
  change e.inv ((colimit.ι (D ⋙ E) m) y) = E.map (colimit.ι D m) y at h
  rw [hy] at h
  change E.map (colimit.ι D m) y = z
  simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply] using h.symm

#print axioms subdivisionLimitPresheaf_section_exists
/-- Each supported subdivision-limit sheaf section has finite-stage representatives near every point.
Source: Bredon, Sheaf Theory, second edition, VI.12; sheafification of supported subdivision limits.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheaf_section_locally_finite (X : TopCat.{0}) (n : ℕ) (U : Opens X)
    (s : ((subdivisionLimitSheafComplex X).X n).obj.obj (Opposite.op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hV : V ≤ U) (m : ℕ)
      (y : ((singularChainPresheafComplex ℚ X).X n).obj (Opposite.op V)),
      x ∈ V ∧
      ((toSheafify (Opens.grothendieckTopology X) ((subdivisionLimitPresheafComplex X).X n)).app
        (Opposite.op V))
        ((((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op V)) y) =
      ((subdivisionLimitSheafComplex X).X n).obj.map (homOfLE hV).op s := by
  let P := (subdivisionLimitPresheafComplex X).X n
  let f := toSheafify (Opens.grothendieckTopology X) P
  have h : TopCat.Presheaf.IsLocallySurjective f := by
    change CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f
    infer_instance
  obtain ⟨V, hV, ⟨z, hz⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff f).mp h U s x hx
  obtain ⟨m, y, hy⟩ := subdivisionLimitPresheaf_section_exists X n V z
  refine ⟨V, hV, m, y, hxV, ?_⟩
  rw [hy]
  exact hz

#print axioms subdivisionLimitSheaf_section_locally_finite
/-- Subdivision-limit sheaf sections locally come from actual ambient singular chains at finite stages.
Source: Bredon, Sheaf Theory, second edition, VI.12; local supported-chain representatives.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheaf_section_locally_ambient (X : TopCat.{0}) (n : ℕ) (U : Opens X)
    (s : ((subdivisionLimitSheafComplex X).X n).obj.obj (Opposite.op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hV : V ≤ U) (m : ℕ) (z : (SingularChainComplex ℚ X).X n),
      x ∈ V ∧
      ((toSheafify (Opens.grothendieckTopology X) ((subdivisionLimitPresheafComplex X).X n)).app
        (Opposite.op V))
        ((((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op V))
          ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n z)) =
      ((subdivisionLimitSheafComplex X).X n).obj.map (homOfLE hV).op s := by
  obtain ⟨V, hV, m, y, hxV, hy⟩ := subdivisionLimitSheaf_section_locally_finite X n U s x hx
  obtain ⟨z, hz⟩ := relativeChainProjection_surjective
    (TopPair.ofSubset (X := X) (V : Set X)ᶜ) n y
  refine ⟨V, hV, m, z, hxV, ?_⟩
  rw [hz]
  exact hy

#print axioms subdivisionLimitSheaf_section_locally_ambient
/-- Equality of two finite-stage supported sections in the actual presheaf limit occurs at a later finite stage.
Source: Bredon, Sheaf Theory, second edition, VI.12; equality in the filtered subdivision limit.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitPresheaf_section_eq_eventually (X : TopCat.{0}) (n m : ℕ) (U : Opens X)
    (z w : ((singularChainPresheafComplex ℚ X).X n).obj (Opposite.op U))
    (h : (((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op U)) z =
      (((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op U)) w) :
    ∃ (k : ℕ) (hk : m ≤ k),
      ((((presheafSubdivisionDiagram X).map (homOfLE hk)).f n).app (Opposite.op U)) z =
        ((((presheafSubdivisionDiagram X).map (homOfLE hk)).f n).app (Opposite.op U)) w := by
  let D := presheafSubdivisionDiagram X
  let E : ChainComplex (TopCat.Presheaf AddCommGrpCat.{0} X) ℕ ⥤ AddCommGrpCat.{0} :=
    HomologicalComplex.eval (TopCat.Presheaf AddCommGrpCat.{0} X) (ComplexShape.down ℕ) n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (Opposite.op U)
  letI : PreservesColimit D E := by
    dsimp only [D, E, TopCat.Presheaf]
    infer_instance
  have hc : ((E.mapCocone (colimit.cocone D)).ι.app m) z =
      ((E.mapCocone (colimit.cocone D)).ι.app m) w := h
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq (D ⋙ E)
    (isColimitOfPreserves E (colimit.isColimit D)) z w hc
  refine ⟨k, leOfHom f, ?_⟩
  have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
  have hg : g = homOfLE (leOfHom f) := Subsingleton.elim _ _
  change E.map (D.map (homOfLE (leOfHom f))) z = E.map (D.map (homOfLE (leOfHom f))) w
  change E.map (D.map f) z = E.map (D.map g) w at hfg
  rw [hf, hg] at hfg
  exact hfg

#print axioms subdivisionLimitPresheaf_section_eq_eventually
end HodgeLean.Foundations.RationalHomologyManifold

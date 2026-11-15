import HodgeLean.Foundations.Topology.RationalSheafComparisonDefs

/-! Composition compatibility for mapping and extending cochain complexes.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Topology.RationalSheafComparison

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem mapExtendCanonicalIso_comp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] (K : CochainComplex C ℕ) :
    (HomologicalComplex.mapExtendCanonicalIso (F ⋙ G) K ComplexShape.embeddingUpNat).hom =
      (G.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapExtendCanonicalIso F K ComplexShape.embeddingUpNat).hom ≫
      (HomologicalComplex.mapExtendCanonicalIso G
        ((F.mapHomologicalComplex (.up ℕ)).obj K) ComplexShape.embeddingUpNat).hom := by
  apply HomologicalComplex.Hom.ext
  funext j
  by_cases hj : 0 ≤ j
  · lift j to ℕ using hj
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.mapExtendCanonicalIso_hom_f (F ⋙ G) K ComplexShape.embeddingUpNat
        (i := j) (j := (j : ℤ)) rfl,
      HomologicalComplex.mapExtendCanonicalIso_hom_f F K ComplexShape.embeddingUpNat
        (i := j) (j := (j : ℤ)) rfl,
      HomologicalComplex.mapExtendCanonicalIso_hom_f G ((F.mapHomologicalComplex (.up ℕ)).obj K)
        ComplexShape.embeddingUpNat (i := j) (j := (j : ℤ)) rfl,
      Functor.comp_map, Functor.map_comp, Category.assoc]
    erw [← G.map_comp_assoc
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso ComplexShape.embeddingUpNat (i := j) (i' := (j : ℤ)) rfl).inv
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso ComplexShape.embeddingUpNat (i := j) (i' := (j : ℤ)) rfl).hom]
    rw [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  · exact (((G.mapHomologicalComplex (.up ℕ)).obj
      ((F.mapHomologicalComplex (.up ℕ)).obj K)).isZero_extend_X
        ComplexShape.embeddingUpNat j (by
          intro i hi
          exact hj (show 0 ≤ j from hi ▸ Int.natCast_nonneg i))).eq_of_tgt _ _

end HodgeLean.Topology.RationalSheafComparison

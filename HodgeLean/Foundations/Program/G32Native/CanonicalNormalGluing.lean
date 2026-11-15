import HodgeLean.Foundations.Program.G32Native.EtaleLocusConormal
import HodgeLean.Foundations.AlgebraicGeometry.ConormalLocalIsomorphism

/-! # Retained conormal models on coefficient charts and etale sheets

The model morphism and its chart formulas are explicit inputs. In particular,
this file supplies no canonical normal-calculation producer.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A specified model morphism invertible on the retained coefficient charts
is a global isomorphism of actual conormal sheaves.
Source: Hartshorne, Algebraic Geometry, II.5, stalk criterion for isomorphisms. -/
def coefficientChartModelIso
    {P B : Scheme.{0}} (i : P ⟶ B) (M : P.Modules)
    (a : Conormal.sheaf i ⟶ M) {I : Type} (U : I → P.Opens)
    (hcover : ∀ x : P, ∃ t, x ∈ U t)
    (chart : ∀ t, (Scheme.Modules.pullback (U t).ι).obj (Conormal.sheaf i) ≅
      (Scheme.Modules.pullback (U t).ι).obj M)
    (hchart : ∀ t, (Scheme.Modules.pullback (U t).ι).map a = (chart t).hom) :
    Conormal.sheaf i ≅ M := by
  have : IsIso a := Conormal.moduleMap_isIso_of_open_neighborhoods a (by
    intro x
    obtain ⟨t, ht⟩ := hcover x
    refine ⟨U t, ht, ?_⟩
    rw [hchart t]
    infer_instance)
  exact asIso a

/-- The sheet model uses the same base model and the same specified source map.
Source: Hartshorne, Algebraic Geometry, II.8, conormal localization and flat base change. -/
def etaleSheetModelIso
    {Q P W B : Over (Spec ↧ℂ)} (i : P ⟶ B) [IsClosedImmersion i.left]
    (β : W ⟶ B) (U : B.left.Opens) (hU : Set.range i.left ⊆ U)
    (het : Etale (β.left ∣_ U)) (g : Q ⟶ P) [IsIso g.left]
    (j : Q ⟶ W) [IsClosedImmersion j.left] (h : g ≫ i = j ≫ β)
    (M : P.left.Modules) (producer : Conormal.sheaf i.left ≅ M) :
    Conormal.sheaf j.left ≅ (Scheme.Modules.pullback g.left).obj M :=
  Classical.choice (s2e_i1_etale_locus_component_conormalIso i β U hU het g j h) ≪≫
    (Scheme.Modules.pullback g.left).mapIso producer

/-- Every coefficient-chart formula survives transport to the same sheet.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, functoriality of module pullback. -/
theorem etaleSheetModelIso_chart
    {Q P W B : Over (Spec ↧ℂ)} (i : P ⟶ B) [IsClosedImmersion i.left]
    (β : W ⟶ B) (U : B.left.Opens) (hU : Set.range i.left ⊆ U)
    (het : Etale (β.left ∣_ U)) (g : Q ⟶ P) [IsIso g.left]
    (j : Q ⟶ W) [IsClosedImmersion j.left] (h : g ≫ i = j ≫ β)
    (M : P.left.Modules) (producer : Conormal.sheaf i.left ≅ M)
    (V : Q.left.Opens) :
    (Scheme.Modules.pullback V.ι).map
        (etaleSheetModelIso i β U hU het g j h M producer).hom =
      (Scheme.Modules.pullback V.ι).map
        (Classical.choice
          (s2e_i1_etale_locus_component_conormalIso i β U hU het g j h)).hom ≫
      (Scheme.Modules.pullback V.ι).map
        ((Scheme.Modules.pullback g.left).map producer.hom) := by
  exact (Scheme.Modules.pullback V.ι).map_comp _ _

/-- Transition maps defined by the retained frames satisfy the overlap cocycle.
Source: Hartshorne, Algebraic Geometry, II.5, transition maps for a module sheaf. -/
theorem coefficient_overlap_cocycle
    {X : Scheme.{0}} {N M₀ M₁ M₂ : X.Modules}
    (e₀ : N ≅ M₀) (e₁ : N ≅ M₁) (e₂ : N ≅ M₂) :
    (e₀.symm ≪≫ e₁).hom ≫ (e₁.symm ≪≫ e₂).hom = (e₀.symm ≪≫ e₂).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

#print axioms coefficientChartModelIso
#print axioms etaleSheetModelIso
#print axioms etaleSheetModelIso_chart
#print axioms coefficient_overlap_cocycle
end HodgeLean.Foundations.Program.G32Native

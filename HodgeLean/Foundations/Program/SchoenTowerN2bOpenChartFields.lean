import Mathlib.AlgebraicGeometry.FunctionField
import HodgeLean.Foundations.Program.SchoenTowerN2aProofs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The function-field isomorphism induced by an actual open chart inclusion.
Source: Hartshorne, Algebraic Geometry, II.3. -/
def n2b_openChartFunctionFieldIso {U X : Scheme.{0}} [IsIntegral U] [IsIntegral X]
    (j : U ⟶ X) [IsOpenImmersion j] : X.functionField ≅ U.functionField :=
  eqToIso (congrArg X.presheaf.stalk (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint U))

/-- The rational function represented by a section on the specified open chart.
Source: Hartshorne, Algebraic Geometry, II.3. -/
def n2b_openChartRationalMap {U X : Scheme.{0}} [IsIntegral U] [IsIntegral X]
    (j : U ⟶ X) [IsOpenImmersion j] : Γ(U, ⊤) →+* X.functionField := by
  letI : Nonempty (⊤ : U.Opens) := ⟨⟨genericPoint U, trivial⟩⟩
  exact (U.germToFunctionField ⊤ ≫ (n2b_openChartFunctionFieldIso j).inv).hom

theorem n2b_openChartRationalMap_injective {U X : Scheme.{0}}
    [IsIntegral U] [IsIntegral X] (j : U ⟶ X) [IsOpenImmersion j] :
    Function.Injective (n2b_openChartRationalMap j) := by
  letI : Nonempty (⊤ : U.Opens) := ⟨⟨genericPoint U, trivial⟩⟩
  exact (n2b_openChartFunctionFieldIso j).symm.commRingCatIsoToRingEquiv.injective.comp
    (U.germToFunctionField_injective ⊤)

/-- The chart function-field identification preserves the actual section coefficient maps. -/
theorem n2b_openChartFunctionField_germ_square {U X : Scheme.{0}}
    [IsIntegral U] [IsIntegral X] (j : U ⟶ X) [IsOpenImmersion j]
    (V : X.Opens) (hx : genericPoint X ∈ V) :
    X.presheaf.germ V (genericPoint X) hx ≫ (n2b_openChartFunctionFieldIso j).hom =
      j.app V ≫ U.presheaf.germ (j ⁻¹ᵁ V) (genericPoint U)
        (by change j (genericPoint U) ∈ V
            rw [genericPoint_eq_of_isOpenImmersion j]
            exact hx) := by
  change _ ≫ (eqToHom (congrArg X.presheaf.stalk
    (genericPoint_eq_of_isOpenImmersion j).symm) ≫ j.stalkMap (genericPoint U)) = _
  rw [← Category.assoc, n2a_germ_transport _ _ _ (genericPoint_eq_of_isOpenImmersion j)]
  exact j.germ_stalkMap V _ _

/-- The actual chart function-field isomorphisms respect composition of chart inclusions. -/
theorem n2b_openChartFunctionFieldIso_comp {V U X : Scheme.{0}}
    [IsIntegral V] [IsIntegral U] [IsIntegral X]
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] :
    (n2b_openChartFunctionFieldIso (i ≫ j)).hom =
      (n2b_openChartFunctionFieldIso j).hom ≫ (n2b_openChartFunctionFieldIso i).hom := by
  let hi := genericPoint_eq_of_isOpenImmersion i
  let hj := genericPoint_eq_of_isOpenImmersion j
  let hij := genericPoint_eq_of_isOpenImmersion (i ≫ j)
  have ht (x y : U) (h : x = y) :
      eqToHom (congrArg X.presheaf.stalk (congrArg j h)) ≫ j.stalkMap y =
        j.stalkMap x ≫ eqToHom (congrArg U.presheaf.stalk h) := by
    cases h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have heq : eqToHom (congrArg X.presheaf.stalk hij.symm) =
      eqToHom (congrArg X.presheaf.stalk hj.symm) ≫
        eqToHom (congrArg X.presheaf.stalk (congrArg j hi.symm)) := by
    rw [eqToHom_trans]
  change eqToHom (congrArg X.presheaf.stalk hij.symm) ≫
      (i ≫ j).stalkMap (genericPoint V) =
    (eqToHom (congrArg X.presheaf.stalk hj.symm) ≫ j.stalkMap (genericPoint U)) ≫
      (eqToHom (congrArg U.presheaf.stalk hi.symm) ≫ i.stalkMap (genericPoint V))
  rw [Scheme.Hom.stalkMap_comp, heq]
  calc
    _ = eqToHom (congrArg X.presheaf.stalk hj.symm) ≫
        ((eqToHom (congrArg X.presheaf.stalk (congrArg j hi.symm)) ≫
          j.stalkMap (i (genericPoint V))) ≫ i.stalkMap (genericPoint V)) := by
      simp only [Category.assoc]
    _ = eqToHom (congrArg X.presheaf.stalk hj.symm) ≫
        ((j.stalkMap (genericPoint U) ≫ eqToHom (congrArg U.presheaf.stalk hi.symm)) ≫
          i.stalkMap (genericPoint V)) := by
      rw [ht (genericPoint U) (i (genericPoint V)) hi.symm]
    _ = _ := by simp only [Category.assoc]

/-- Restriction to a smaller actual chart preserves the represented rational function. -/
theorem n2b_openChartRationalMap_restrict {V U X : Scheme.{0}}
    [IsIntegral V] [IsIntegral U] [IsIntegral X]
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (a : Γ(U, ⊤)) :
    n2b_openChartRationalMap (i ≫ j) (i.appTop.hom a) = n2b_openChartRationalMap j a := by
  letI : Nonempty (⊤ : U.Opens) := ⟨⟨genericPoint U, trivial⟩⟩
  letI : Nonempty (⊤ : V.Opens) := ⟨⟨genericPoint V, trivial⟩⟩
  have hs : U.germToFunctionField ⊤ ≫ (n2b_openChartFunctionFieldIso i).hom =
      i.appTop ≫ V.germToFunctionField ⊤ :=
    n2b_openChartFunctionField_germ_square i ⊤ trivial
  have he : n2b_openChartFunctionFieldIso (i ≫ j) =
      n2b_openChartFunctionFieldIso j ≪≫ n2b_openChartFunctionFieldIso i := by
    apply Iso.ext
    exact n2b_openChartFunctionFieldIso_comp i j
  have h : i.appTop ≫ (V.germToFunctionField ⊤ ≫
        (n2b_openChartFunctionFieldIso (i ≫ j)).inv) =
      U.germToFunctionField ⊤ ≫ (n2b_openChartFunctionFieldIso j).inv := by
    rw [he, Iso.trans_inv]
    calc
      _ = (i.appTop ≫ V.germToFunctionField ⊤) ≫
          ((n2b_openChartFunctionFieldIso i).inv ≫
            (n2b_openChartFunctionFieldIso j).inv) := by simp only [Category.assoc]
      _ = (U.germToFunctionField ⊤ ≫ (n2b_openChartFunctionFieldIso i).hom) ≫
          ((n2b_openChartFunctionFieldIso i).inv ≫
            (n2b_openChartFunctionFieldIso j).inv) := by rw [← hs]
      _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun f => f.hom a) h

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Curves.Picard.LineBundles.Transport

/-! # Sections of the actual tensor product

Pure tensors enter the sheafified module through the adjunction unit.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The actual map from sectionwise tensors to their sheafification. -/
def tensorPresheafUnit {X : Scheme} (M N : X.Modules) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := X.presheaf) M.val N.val ⟶ (tensor M N).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

/-- A pure tensor gives a section of the literal sheafified tensor product. -/
def tensorSection {X : Scheme} (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) : Γ(tensor M N, U) :=
  (tensorPresheafUnit M N).app (Opposite.op U) (s ⊗ₜ[Γ(X, U)] t)

/-- Actual tensor sections are additive in their first argument. -/
theorem tensorSection_add_left {X : Scheme} (M N : X.Modules) (U : X.Opens)
    (s u : Γ(M, U)) (t : Γ(N, U)) :
    tensorSection M N U (s + u) t = tensorSection M N U s t + tensorSection M N U u t := by
  simp only [tensorSection, TensorProduct.add_tmul, map_add]

/-- Actual tensor sections are additive in their second argument. -/
theorem tensorSection_add_right {X : Scheme} (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t u : Γ(N, U)) :
    tensorSection M N U s (t + u) = tensorSection M N U s t + tensorSection M N U s u := by
  simp only [tensorSection, TensorProduct.tmul_add, map_add]

/-- Actual tensor sections preserve scalars in their first argument. -/
theorem tensorSection_smul_left {X : Scheme} (M N : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    tensorSection M N U (a • s) t = a • tensorSection M N U s t := by
  change (tensorPresheafUnit M N).app (Opposite.op U) (a • (s ⊗ₜ[Γ(X, U)] t)) = _
  exact (tensorPresheafUnit M N).app (Opposite.op U) |>.hom.map_smul a _

/-- Actual tensor sections preserve scalars in their second argument. -/
theorem tensorSection_smul_right {X : Scheme} (M N : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    tensorSection M N U s (a • t) = a • tensorSection M N U s t := by
  simp only [tensorSection, TensorProduct.tmul_smul]
  exact (tensorPresheafUnit M N).app (Opposite.op U) |>.hom.map_smul a _

/-- Actual tensor sections commute with restriction. -/
theorem tensorSection_restrict {X : Scheme} (M N : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (s : Γ(M, U)) (t : Γ(N, U)) :
    (tensor M N).presheaf.map (homOfLE h).op (tensorSection M N U s t) =
      tensorSection M N V (M.presheaf.map (homOfLE h).op s)
        (N.presheaf.map (homOfLE h).op t) := by
  exact (PresheafOfModules.naturality_apply (tensorPresheafUnit M N)
    (homOfLE h).op (s ⊗ₜ[Γ(X, U)] t)).symm

/-- Tensor maps act on actual pure tensor sections componentwise. -/
theorem tensorMap_section {X : Scheme} {M N P Q : X.Modules}
    (f : M ⟶ N) (g : P ⟶ Q) (U : X.Opens) (s : Γ(M, U)) (t : Γ(P, U)) :
    (tensorMap f g).app U (tensorSection M P U s t) =
      tensorSection N Q U (f.app U s) (g.app U t) := by
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom f.val g.val)
  have hh := congrArg (fun h => h.app (Opposite.op U) (s ⊗ₜ[Γ(X, U)] t)) hn
  exact hh.symm

/-- Morphisms from the actual tensor sheaf are determined by their pure tensor sections. -/
theorem tensor_hom_ext {X : Scheme} {M N P : X.Modules}
    {f g : tensor M N ⟶ P}
    (h : ∀ (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)),
      f.app U (tensorSection M N U s t) = g.app U (tensorSection M N U s t)) : f = g := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h U.unop s t

end HodgeLean.Foundations.Curves.Picard.LineBundles

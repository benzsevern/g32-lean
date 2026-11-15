import HodgeLean.Adapters.IntersectionProductMovingCoords

/-! # Product charts of fibre products over the integers

For open immersions `Spec R ⟶ A` and `Spec S ⟶ B`, the fibre product `A × B` over the terminal
scheme (that is, over `Spec ℤ`) contains `Spec (R ⊗[ℤ] S)` as an open subscheme whose underlying
set is `pr₁⁻¹(range) ∩ pr₂⁻¹(range)`, and the projections restrict to `Spec` of the two
inclusions into the tensor product. The projective space `ProjectiveSpace n S` of the upstream
library is such a fibre product, as is `ProjectiveSpace (Fin 2) X`.

Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (construction of fibre products from
affine pieces); Mathlib, `AlgebraicGeometry.pullbackSpecIso`, `Scheme.Pullback.range_map`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace HodgeLean.Adapters

/-- `Spec R × Spec S ≅ Spec (R ⊗[ℤ] S)` over the terminal scheme. -/
def a3m_tensorIso (R S : CommRingCat.{0}) :
    pullback (terminal.from (Spec R)) (terminal.from (Spec S)) ≅
      Spec (.of (TensorProduct ℤ R S)) :=
  let e := terminalIsTerminal.uniqueUpToIso specZIsTerminal
  (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) e.hom
    (specZIsTerminal.hom_ext _ _) (specZIsTerminal.hom_ext _ _))) ≪≫
    pullbackSpecIso ℤ _ _

theorem a3m_tensorIso_hom_fst (R S : CommRingCat.{0}) :
    (a3m_tensorIso R S).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := R) (B := S))) =
      pullback.fst (terminal.from (Spec R)) (terminal.from (Spec S)) := by
  simp [a3m_tensorIso]

theorem a3m_tensorIso_hom_snd (R S : CommRingCat.{0}) :
    (a3m_tensorIso R S).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := R) (B := S)).toRingHom) =
      pullback.snd (terminal.from (Spec R)) (terminal.from (Spec S)) := by
  simp [a3m_tensorIso]

section Chart

variable {A B : Scheme.{0}} {R S : CommRingCat.{0}} (ιA : Spec R ⟶ A) (ιB : Spec S ⟶ B)

/-- The product chart `Spec (R ⊗[ℤ] S) ⟶ A × B` of two charts. -/
def a3m_prodChart :
    Spec (.of (TensorProduct ℤ R S)) ⟶ pullback (terminal.from A) (terminal.from B) :=
  (a3m_tensorIso R S).inv ≫ pullback.map _ _ _ _ ιA ιB (𝟙 _)
    (terminalIsTerminal.hom_ext _ _) (terminalIsTerminal.hom_ext _ _)

instance a3m_prodChart_isOpenImmersion [IsOpenImmersion ιA] [IsOpenImmersion ιB] :
    IsOpenImmersion (a3m_prodChart ιA ιB) := by
  unfold a3m_prodChart; infer_instance

theorem a3m_prodChart_fst :
    a3m_prodChart ιA ιB ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := R)
        (B := S))) ≫ ιA := by
  rw [a3m_prodChart, Category.assoc, pullback.lift_fst, ← a3m_tensorIso_hom_fst R S,
    Category.assoc, Iso.inv_hom_id_assoc]

theorem a3m_prodChart_snd :
    a3m_prodChart ιA ιB ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ℤ) (A := R)
        (B := S)).toRingHom) ≫ ιB := by
  rw [a3m_prodChart, Category.assoc, pullback.lift_snd, ← a3m_tensorIso_hom_snd R S,
    Category.assoc, Iso.inv_hom_id_assoc]

theorem a3m_range_prodChart :
    Set.range (a3m_prodChart ιA ιB) =
      pullback.fst (terminal.from A) (terminal.from B) ⁻¹' Set.range ιA ∩
        pullback.snd (terminal.from A) (terminal.from B) ⁻¹' Set.range ιB := by
  rw [a3m_prodChart, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.2 (a3m_tensorIso R S).inv.surjective, Set.image_univ,
    Scheme.Pullback.range_map]

end Chart

end HodgeLean.Adapters

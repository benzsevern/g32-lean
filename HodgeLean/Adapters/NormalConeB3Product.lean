import HodgeLean.Adapters.NormalConeB3Defs

/-! # Diagonal cone coefficient: the product of an affine open with itself

For an affine open `V` of a scheme over a field, `pr₁⁻¹ V ∩ pr₂⁻¹ V ⊂ Y ×ₖ Y` is affine with ring of
sections `Γ(V) ⊗ₖ Γ(V)`, through the comparison map `a3b3_tangentToProduct`.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry TensorProduct
universe u

section product
variable {k : Type u} [Field k] {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k))

private theorem a3b3_toSpecΓ_fieldMap_aux (V : Y.Opens) (h : V ≤ p ⁻¹ᵁ ⊤) :
    V.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V h) =
      V.ι ≫ p := by
  rw [Spec.map_comp, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, Scheme.Opens.toSpecΓ_top,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id,
    Scheme.Hom.resLE_comp_ι]

/-- An open lies over the base point through the spectrum of its scalars.
Source: Mathlib, `Scheme.Opens.toSpecΓ_SpecMap_appLE` and `toSpecΓ_SpecMap_ΓSpecIso_inv`. -/
theorem a3b3_toSpecΓ_fieldMap (V : Y.Opens) :
    V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (a3b2_fieldMap k Y p V)) = V.ι ≫ p :=
  a3b3_toSpecΓ_fieldMap_aux p V _

/-- The open immersion `V ×ₖ V ⟶ Y ×ₖ Y` of an open `V` (implementation). -/
private def a3b3_prodMap (V : Y.Opens) : pullback (V.ι ≫ p) (V.ι ≫ p) ⟶ pullback p p :=
  pullback.map _ _ p p V.ι V.ι (𝟙 _) (by simp) (by simp)

private theorem a3b3_range_prodMap (V : Y.Opens) (W : (pullback p p : Scheme.{u}).Opens)
    (hW : W = pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ V) :
    Set.range W.ι = Set.range (a3b3_prodMap p V) := by
  rw [Scheme.Opens.range_ι, a3b3_prodMap, Scheme.Pullback.range_map, hW]
  simp [Scheme.Opens.range_ι]

/-- For an affine open `V` of a scheme over a field, `W = pr₁⁻¹ V ∩ pr₂⁻¹ V` is affine and the
comparison map `Γ(V) ⊗ₖ Γ(V) → Γ(W)` is bijective: `W ≅ V ×ₖ V ≅ Spec (Γ(V) ⊗ₖ Γ(V))`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 and its proof; Mathlib,
`pullbackSpecIso` and `Scheme.Pullback.range_map`. -/
theorem a3b3_tangentToProduct_bijective (V : Y.Opens) (hV : IsAffineOpen V)
    (W : (pullback p p : Scheme.{u}).Opens)
    (hW : W = pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ V) :
    IsAffineOpen W ∧ Function.Bijective (a3b3_tangentToProduct p V W hW) := by
  let := (a3b2_fieldMap k Y p V).toAlgebra
  have hq : V.ι ≫ p = hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, V))) :=
    by rw [IsAffineOpen.isoSpec_hom]; exact (a3b3_toSpecΓ_fieldMap p V).symm
  have : IsOpenImmersion (a3b3_prodMap p V) := by unfold a3b3_prodMap; infer_instance
  let eW := IsOpenImmersion.isoOfRangeEq W.ι (a3b3_prodMap p V) (a3b3_range_prodMap p V W hW)
  let m := pullback.map (V.ι ≫ p) (V.ι ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, V))))
    (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, V)))) hV.isoSpec.hom hV.isoSpec.hom (𝟙 _)
    (by rw [Category.comp_id, hq]) (by rw [Category.comp_id, hq])
  let ψ := eW.hom ≫ m ≫ (pullbackSpecIso k Γ(Y, V) Γ(Y, V)).hom
  have hψ : IsIso ψ := inferInstance
  have hfst : (pullback.fst p p).resLE V W (hW ▸ inf_le_left) =
      eW.hom ≫ pullback.fst (V.ι ≫ p) (V.ι ≫ p) := by
    rw [← cancel_mono V.ι, Scheme.Hom.resLE_comp_ι, Category.assoc]
    have : pullback.fst (V.ι ≫ p) (V.ι ≫ p) ≫ V.ι = a3b3_prodMap p V ≫ pullback.fst p p := by
      simp [a3b3_prodMap]
    rw [this, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  have hsnd : (pullback.snd p p).resLE V W (hW ▸ inf_le_right) =
      eW.hom ≫ pullback.snd (V.ι ≫ p) (V.ι ≫ p) := by
    rw [← cancel_mono V.ι, Scheme.Hom.resLE_comp_ι, Category.assoc]
    have : pullback.snd (V.ι ≫ p) (V.ι ≫ p) ≫ V.ι = a3b3_prodMap p V ≫ pullback.snd p p := by
      simp [a3b3_prodMap]
    rw [this, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  have key : W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (a3b3_tangentToProduct p V W hW)) = ψ := by
    rw [← cancel_mono (pullbackSpecIso k Γ(Y, V) Γ(Y, V)).inv]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      have : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
          CommRingCat.ofHom (a3b3_tangentToProduct p V W hW) =
            (pullback.fst p p).appLE V W (hW ▸ inf_le_left) := by
        ext a
        change a3b3_tangentToProduct p V W hW (a ⊗ₜ[k] 1) = _
        rw [a3b3_tangentToProduct_tmul, map_one, mul_one]
      rw [this, Scheme.Opens.toSpecΓ_SpecMap_appLE, hfst]
      simp [ψ, m, IsAffineOpen.isoSpec_hom]
    · rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      have : CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k) (A := Γ(Y, V))
          (B := Γ(Y, V))).toRingHom ≫ CommRingCat.ofHom (a3b3_tangentToProduct p V W hW) =
            (pullback.snd p p).appLE V W (hW ▸ inf_le_right) := by
        ext a
        change a3b3_tangentToProduct p V W hW (1 ⊗ₜ[k] a) = _
        rw [a3b3_tangentToProduct_tmul, map_one, one_mul]
      erw [this]
      rw [Scheme.Opens.toSpecΓ_SpecMap_appLE, hsnd]
      simp [ψ, m, IsAffineOpen.isoSpec_hom]
  have hWaff : IsAffineOpen W := IsAffine.of_isIso ψ
  refine ⟨hWaff, ?_⟩
  have h1 : IsIso (Spec.map (CommRingCat.ofHom (a3b3_tangentToProduct p V W hW))) := by
    have : IsIso W.toSpecΓ := inferInstanceAs (IsIso hWaff.isoSpec.hom)
    have e : Spec.map (CommRingCat.ofHom (a3b3_tangentToProduct p V W hW)) =
        inv W.toSpecΓ ≫ ψ := by
      rw [IsIso.eq_inv_comp]; exact key
    rw [e]
    infer_instance
  have h2 : IsIso (CommRingCat.ofHom (a3b3_tangentToProduct p V W hW)).op :=
    have : IsIso (Scheme.Spec.map (CommRingCat.ofHom (a3b3_tangentToProduct p V W hW)).op) := h1
    isIso_of_reflects_iso _ Scheme.Spec
  have : IsIso (CommRingCat.ofHom (a3b3_tangentToProduct p V W hW)) := (isIso_op_iff _).mp h2
  exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (a3b3_tangentToProduct p V W hW))

end product
end HodgeLean.Adapters

import HodgeLean.Foundations.QuotientDuality.LocalOverlapPointTransport
import HodgeLean.Foundations.QuotientDuality.LocalOpenRestrictionMap
import HodgeLean.Foundations.QuotientDuality.LocalEmbeddingAtlasOrientation
import HodgeLean.Foundations.QuotientDuality.LocalCoherentComplexNormalization

/-! Gluing the complex-normalized orientations of actual affine neighborhoods. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem complex_affine_local_orientations_glue
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ)
    (hloc : ∀ x : ComplexPoint X, ∃ U : X.left.affineOpens, x.underlying ∈ U.1 ∧
      Nonempty (LocalRationalOrientation (TopCat.of (ComplexPoint (openScheme X U.1))) (2 * d))) :
    Nonempty (LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d)) := by
  classical
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : IsNoetherian X.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace X.hom }
  letI : NoetherianSpace X.left := IsNoetherian.noetherianSpace
  choose U hx hu using hloc
  let A (i : ComplexPoint X) := openScheme X (U i).1
  let f (i : ComplexPoint X) := openInclusion X (U i).1
  letI (i : ComplexPoint X) : IsAffine (A i).left := (U i).2
  letI (i : ComplexPoint X) : Nonempty (U i).1 := ⟨⟨i.underlying, hx i⟩⟩
  letI (i : ComplexPoint X) : Nonempty (A i).left := inferInstanceAs (Nonempty (U i).1)
  letI (i : ComplexPoint X) : IsIntegral (A i).left := isIntegral_of_isOpenImmersion (U i).1.ι
  letI (i : ComplexPoint X) : LocallyOfFiniteType (A i).hom :=
    inferInstanceAs (LocallyOfFiniteType ((U i).1.ι ≫ X.hom))
  letI (i : ComplexPoint X) : NoetherianSpace (A i).left :=
    (U i).1.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI (i : ComplexPoint X) : QuasiCompact (A i).hom := inferInstance
  letI (i : ComplexPoint X) : IsSeparated (A i).hom :=
    inferInstanceAs (IsSeparated ((U i).1.ι ≫ X.hom))
  letI (i : ComplexPoint X) : T2Space (ComplexPoint (A i)) := f4_t2Space (A i)
  have hn (i : ComplexPoint X) := normalize_coherent_complex_orientation (A i) d (Classical.choice (hu i))
  choose o ho using hn
  apply open_embedding_atlas_coherent_orientation (TopCat.of (ComplexPoint X)) (2 * d)
    (ComplexPoint X) (fun i => TopCat.of (ComplexPoint (A i)))
    (fun i => TopCat.ofHom (Point.continuousMap (f i)))
    (fun i => HodgeLean.Foundations.ComplexTopology.openImmersion_points (f i)) o
  · intro x
    let a := asOpenPoint X (U x).1 x (hx x)
    exact ⟨x, a, congrArg Subtype.val ((openHomeomorph X (U x).1).apply_symm_apply ⟨x, hx x⟩)⟩
  · intro i j a b hab
    change Point.map (f i) a = Point.map (f j) b at hab
    have hUi : (Point.map (f i) a).underlying ∈ (U i).1 := a.underlying.property
    have hUj : (Point.map (f i) a).underlying ∈ (U j).1 := by
      rw [hab]
      exact b.underlying.property
    let V := (U i).1 ⊓ (U j).1
    let S := openScheme X V
    letI : Nonempty V := ⟨⟨(Point.map (f i) a).underlying, ⟨hUi, hUj⟩⟩⟩
    letI : Nonempty S.left := inferInstanceAs (Nonempty V)
    letI : IsIntegral S.left := isIntegral_of_isOpenImmersion V.ι
    letI : LocallyOfFiniteType S.hom := inferInstanceAs (LocallyOfFiniteType (V.ι ≫ X.hom))
    letI : NoetherianSpace S.left := V.ι.isOpenEmbedding.isInducing.noetherianSpace
    letI : QuasiCompact S.hom := inferInstance
    letI : IsSeparated S.hom := inferInstanceAs (IsSeparated (V.ι ≫ X.hom))
    letI : T2Space (ComplexPoint S) := f4_t2Space S
    let g₁ : S ⟶ A i := openRestrictionMap X (inf_le_left : V ≤ (U i).1)
    let g₂ : S ⟶ A j := openRestrictionMap X (inf_le_right : V ≤ (U j).1)
    letI : IsOpenImmersion g₁.left := openRestrictionMap_isOpenImmersion X _
    letI : IsOpenImmersion g₂.left := openRestrictionMap_isOpenImmersion X _
    let z := asOpenPoint X V (Point.map (f i) a) ⟨hUi, hUj⟩
    have hz : Point.map (openInclusion X V) z = Point.map (f i) a :=
      congrArg Subtype.val ((openHomeomorph X V).apply_symm_apply ⟨Point.map (f i) a, ⟨hUi, hUj⟩⟩)
    have hz₁ : Point.map g₁ z = a := by
      apply (HodgeLean.Foundations.ComplexTopology.openImmersion_points (f i)).injective
      rw [← Point.map_comp_apply]
      change Point.map (openRestrictionMap X (inf_le_left : V ≤ (U i).1) ≫
        openInclusion X (U i).1) z = _
      rw [openRestrictionMap_inclusion]
      exact hz
    have hz₂ : Point.map g₂ z = b := by
      apply (HodgeLean.Foundations.ComplexTopology.openImmersion_points (f j)).injective
      rw [← Point.map_comp_apply]
      change Point.map (openRestrictionMap X (inf_le_right : V ≤ (U j).1) ≫
        openInclusion X (U j).1) z = _
      rw [openRestrictionMap_inclusion]
      exact hz.trans hab
    have heq := normalized_open_pullbacks_agree S (A i) (A j) g₁ g₂ d (o i) (o j) (ho i) (ho j) z
    have hsq : g₁ ≫ f i = g₂ ≫ f j := by
      dsimp only [g₁, g₂, f]
      rw [openRestrictionMap_inclusion, openRestrictionMap_inclusion]
    have H := common_open_orientation_transport S (A i) (A j) X g₁ g₂ (f i) (f j)
      hsq (2 * d) (o i) (o j) z heq
    rw [hz₁, hz₂] at H
    exact H

#print axioms complex_affine_local_orientations_glue
end HodgeLean.Foundations.QuotientDuality

/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HodgeConjecture.Definitions.AlgebraicTopology.Support.RelativeCohomologyOpenTransport

/-! Ported, with modifications (imports rewritten to this repository's modules, the `module`
header dropped; the upstream licence and notice are in this directory's `LICENSE` and `NOTICE`), from
upstream's `Other/AlgebraicTopology/Support/RelativeCohomologyOpenTransport.lean`
(HodgeConjecture @ `2ead713`), which this repository does not build. Proofs and names are
upstream's, so importing `Other` alongside this file would clash. -/

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite

namespace AlgebraicTopology.Singular

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : IsOpenEmbedding f)
  (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B)

/-- Inverse transport is literal pullback along the inverse pair homeomorphism. -/
theorem supportRelativeCohomologyPresheafOpenIso_inv_app (n : ℕ) (V : Opens Y)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set Y) B) n) :
    (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv.app (op V) a =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportPairImageIso f hf.isEmbedding (V : Set Y) B S
          (fun y _ => by rw [← hB]; rfl)).inv a := rfl

@[reassoc]
theorem supportOpenEmbeddingSheafificationIso_unit (P : TopCat.Presheaf AddCommGrpCat X) :
    toSheafify (Opens.grothendieckTopology Y) (hf.functor.op ⋙ P) ≫
      (supportOpenEmbeddingSheafificationIso f hf P).hom.hom =
    Functor.whiskerLeft hf.functor.op (toSheafify (Opens.grothendieckTopology X) P) := by
  let : hf.functor.IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    hf.functor_isContinuous
  let : hf.functor.IsCocontinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    hf.functor_isCocontinuous
  exact hf.functor.toSheafify_pullbackSheafificationCompatibility AddCommGrpCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) P

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalization square: actual classes are transported through their literal
pair-homeomorphism pullbacks before application of the ambient sheafification unit. -/
@[reassoc]
theorem supportRelativeCohomologySheafOpenIso_unit (n : ℕ) :
    supportRelativeCohomologyToSheaf Y B n ≫
      (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom =
    (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv ≫
      Functor.whiskerLeft hf.functor.op (supportRelativeCohomologyToSheaf X S n) := by
  change toSheafify _ _ ≫ (sheafifyMap _ _ ≫ _) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    supportOpenEmbeddingSheafificationIso_unit]
  rfl

/-- The open transport preserves the literal sheafification images of local classes. -/
theorem supportRelativeCohomologySheafOpenIso_unit_apply (n : ℕ) (V : Opens Y)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set Y) B) n) :
    (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op V)
      ((supportRelativeCohomologyToSheaf Y B n).app (op V) a) =
    (supportRelativeCohomologyToSheaf X S n).app (op (hf.functor.obj V))
      ((supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv.app (op V) a) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (supportRelativeCohomologySheafOpenIso_unit f hf S B hB n) (op V)) a
  exact h



end AlgebraicTopology.Singular

end

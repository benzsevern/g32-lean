/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HodgeConjecture.Definitions.AlgebraicTopology.Support.RelativeCohomologyOpenTransport
import HodgeLean.RealDefs.Port.OpenTransport

/-! Ported, with modifications (imports rewritten to this repository's modules, the `module`
header dropped, public/expose section markers removed; the upstream licence and notice are in
`HodgeLean/RealDefs/Port/LICENSE` and `NOTICE`), from upstream's `Other/AlgebraicTopology/Support/RelativeCohomologyOpenTransport.lean`
at `2ead713`. -/

/-!
# Actual open-embedding transport of the relative-cohomology sheaf

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Support.RelativeCohomologyOpenTransport`.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite

namespace AlgebraicTopology.Singular

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : IsOpenEmbedding f)
  (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B)

/-- Restriction of the transported section is transport of its actual restriction. -/
theorem supportRelativeCohomologySectionOpenImage_restrict (n : ℕ)
    (s : (supportRelativeCohomologySheaf Y B n).obj.obj (op ⊤)) (V : Opens Y) :
    (supportRelativeCohomologySheaf X S n).obj.map
      (hf.functor.map (homOfLE (show V ≤ ⊤ from le_top))).op
      (supportRelativeCohomologySectionOpenImage f hf S B hB n s) =
    (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op V)
      ((supportRelativeCohomologySheaf Y B n).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op s) := by
  aesop



/-- Restriction to each actual image neighborhood retains the constructed comparison. -/
theorem supportRelativeCohomologySectionOnOpen_restrict (n : ℕ) (U : Opens X)
    (hU : hf.functor.obj ⊤ = U)
    (s : (supportRelativeCohomologySheaf Y B n).obj.obj (op ⊤))
    (V : Opens Y) (hV : hf.functor.obj V ≤ U) :
    (supportRelativeCohomologySheaf X S n).obj.map (homOfLE hV).op
      (supportRelativeCohomologySectionOnOpen f hf S B hB n U hU s) =
    (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op V)
      ((supportRelativeCohomologySheaf Y B n).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op s) := by
  have he : (eqToHom hU.symm).op ≫ (homOfLE hV).op =
      (hf.functor.map (homOfLE (show V ≤ ⊤ from le_top))).op := Subsingleton.elim _ _
  dsimp only [supportRelativeCohomologySectionOnOpen]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, he]
  exact supportRelativeCohomologySectionOpenImage_restrict f hf S B hB n s V

end AlgebraicTopology.Singular

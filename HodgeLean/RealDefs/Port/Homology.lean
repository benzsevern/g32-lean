/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenSheafification

/-! Ported, with modifications (imports rewritten to this repository's modules, the `module`
header dropped; the upstream licence and notice are in this directory's `LICENSE` and `NOTICE`), from
upstream's `Other/AlgebraicTopology/Sheaf/HomologySection.lean` (HodgeConjecture @ `2ead713`), which this repository does
not build. Proofs and names are upstream's, so importing `Other` alongside this file would clash. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace CategoryTheory.ShortComplex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical homology comparison is compatible with composition of exact functors. -/
@[reassoc]
theorem mapHomologyIso_comp_hom (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  rw [(S.homologyData.left.map F).mapHomologyIso_eq G]
  simp only [mapHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  erw [Category.comp_id]
  let γ : LeftHomologyMapData (𝟙 (S.map (F ⋙ G)))
      (S.homologyData.left.map (F ⋙ G)) ((S.homologyData.left.map F).map G) :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by simp
      commπ := by simp }
  simpa only [γ, homologyMap_id, Category.id_comp, Category.comp_id] using
    γ.homologyMap_comm.symm

end CategoryTheory.ShortComplex


end

import HodgeLean.Adapters.KleimanTransverseDefs
import HodgeLean.Adapters.KleimanExpectedCoheight
import HodgeLean.Foundations.GeometricIntegralitySchemes

/-! # Translation transversality: proofs of the frozen statements -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace HodgeLean.Adapters

section Hc9kFibre

open CategoryTheory.MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

variable {X : Over (Spec ↧ℂ)}

/-- The underlying point of a complex point is closed. -/
theorem hc9k_isClosed_underlying [LocallyOfFiniteType X.hom] (t : ComplexPoint X) :
    IsClosed ({t.underlying} : Set X.left) :=
  ((pointEquivClosedPoint X.hom) ⟨t.left, by simp⟩).2

/-- The residue-field point at a complex point factors through that complex point. -/
theorem hc9k_fromSpecResidueField_eq [LocallyOfFiniteType X.hom] (t : ComplexPoint X) :
    X.left.fromSpecResidueField t.underlying =
      Spec.map (residueFieldIsoBase X.hom _ (hc9k_isClosed_underlying t)).inv ≫ t.left := by
  have h : pointOfClosedPoint X.hom _ (hc9k_isClosed_underlying t) = t.left :=
    ext_of_apply_closedPoint_eq X.hom (pointOfClosedPoint_comp _ _ _) (by simp)
      (by erw [pointOfClosedPoint_apply]; rfl)
  rw [← h, pointOfClosedPoint, ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id,
    Category.id_comp]

/-- In the group of maps into `X`, `a⁻¹ b = c` gives `a · c = b`. -/
theorem hc9k_mulRight_of_inv_mul [GrpObj X] {W : Over (Spec ↧ℂ)} (a b : W ⟶ X)
    (t : ComplexPoint X) (h : lift (a ≫ GrpObj.inv) b ≫ MonObj.mul = toUnit W ≫ t) :
    a ≫ (GrpObj.mulRight t).hom = b := by
  have h' : a⁻¹ * b = toUnit W ≫ t := h
  have : a ≫ (GrpObj.mulRight t).hom = a * (toUnit W ≫ t) := by
    simp [GrpObj.mulRight, Hom.mul_def, comp_lift_assoc]
  rw [this, ← h', mul_inv_cancel_left]


/-- In the group of maps into `X`, `a · c = b` gives `a⁻¹ b = c`. -/
theorem hc9k_inv_mul_of_mulRight [GrpObj X] {W : Over (Spec ↧ℂ)} (a b : W ⟶ X)
    (t : ComplexPoint X) (h : a ≫ (GrpObj.mulRight t).hom = b) :
    lift (a ≫ GrpObj.inv) b ≫ MonObj.mul = toUnit W ≫ t := by
  have : a ≫ (GrpObj.mulRight t).hom = a * (toUnit W ≫ t) := by
    simp [GrpObj.mulRight, Hom.mul_def, comp_lift_assoc]
  change a⁻¹ * b = _
  rw [← h, this, inv_mul_cancel_left]

variable [GrpObj X] {A B : Over (Spec ↧ℂ)}

/-- The difference map `(a,b) ↦ a⁻¹b` on a product of two schemes mapping to `X`. -/
def hc9k_diff (α : A ⟶ X) (β : B ⟶ X) : A ⨯ B ⟶ X :=
  lift (Limits.prod.fst ≫ α ≫ GrpObj.inv) (Limits.prod.snd ≫ β) ≫ MonObj.mul

section Fibre

variable (α : A ⟶ X) (β : B ⟶ X) (t : ComplexPoint X)

/-- On the fibre over `t`, the second coordinate is the first one translated by `t`. -/
theorem hc9k_diff_fiber_condition [LocallyOfFiniteType X.hom] :
    (hc9k_diff α β).left.fiberι t.underlying ≫ (Limits.prod.fst : A ⨯ B ⟶ A).left ≫ α.left ≫
        (GrpObj.mulRight t).hom.left =
      (hc9k_diff α β).left.fiberι t.underlying ≫ (Limits.prod.snd : A ⨯ B ⟶ B).left ≫
        β.left := by
  set f := (hc9k_diff α β).left
  let Fo : Over (Spec ↧ℂ) := Over.mk (f.fiberι t.underlying ≫ (A ⨯ B).hom)
  let u : Fo ⟶ A ⨯ B := Over.homMk (f.fiberι t.underlying) rfl
  have hu : u ≫ hc9k_diff α β = toUnit Fo ≫ t := by
    ext
    have h1 : (toUnit Fo).left = Fo.hom := by simp
    have h2 : (A ⨯ B).hom = f ≫ X.hom := (Over.w (hc9k_diff α β)).symm
    change f.fiberι t.underlying ≫ f = (toUnit Fo).left ≫ t.left
    rw [h1]
    change _ = (f.fiberι t.underlying ≫ (A ⨯ B).hom) ≫ t.left
    rw [h2, Category.assoc, Category.assoc, Scheme.Hom.fiber_fac_assoc, ← Category.assoc (X.left.fromSpecResidueField _),
      ← SpecMap_residueFieldIsoBase_inv X.hom _
      (hc9k_isClosed_underlying t), Scheme.Hom.fiber_fac, hc9k_fromSpecResidueField_eq]
  have := hc9k_mulRight_of_inv_mul (u ≫ Limits.prod.fst ≫ α) (u ≫ Limits.prod.snd ≫ β) t
    (by rw [← hu, hc9k_diff, comp_lift_assoc]; simp only [Category.assoc])
  simpa [u] using congrArg Over.Hom.left this


/-- The pullback square cut out by the translated coordinate is commutative over `Spec ℂ`. -/
theorem hc9k_translatePullback_snd_hom :
    pullback.snd (α.left ≫ (GrpObj.mulRight t).hom.left) β.left ≫ B.hom =
      pullback.fst (α.left ≫ (GrpObj.mulRight t).hom.left) β.left ≫ A.hom := by
  rw [← Over.w β, ← pullback.condition_assoc, ← Over.w α, Category.assoc,
    Over.w (GrpObj.mulRight t).hom]

/-- The translated-coordinate pullback as a scheme over `Spec ℂ`. -/
abbrev hc9k_translatePullbackOver : Over (Spec ↧ℂ) :=
  Over.mk (pullback.fst (α.left ≫ (GrpObj.mulRight t).hom.left) β.left ≫ A.hom)

/-- The two coordinates of the translated-coordinate pullback, as a map into `A ⨯ B`. -/
def hc9k_translatePullbackLift : hc9k_translatePullbackOver α β t ⟶ A ⨯ B :=
  Limits.prod.lift (Over.homMk (pullback.fst _ _) rfl)
    (Over.homMk (pullback.snd _ _) (hc9k_translatePullback_snd_hom α β t))

/-- First coordinate of `hc9k_translatePullbackLift`. -/
theorem hc9k_translatePullbackLift_fst :
    (hc9k_translatePullbackLift α β t).left ≫ (Limits.prod.fst : A ⨯ B ⟶ A).left =
      pullback.fst _ _ := by
  rw [← Over.comp_left, hc9k_translatePullbackLift, Limits.prod.lift_fst]
  rfl

/-- Second coordinate of `hc9k_translatePullbackLift`. -/
theorem hc9k_translatePullbackLift_snd :
    (hc9k_translatePullbackLift α β t).left ≫ (Limits.prod.snd : A ⨯ B ⟶ B).left =
      pullback.snd _ _ := by
  rw [← Over.comp_left, hc9k_translatePullbackLift, Limits.prod.lift_snd]
  rfl

/-- The translated-coordinate pullback lies over `t` under the difference map. -/
theorem hc9k_translatePullbackLift_diff :
    hc9k_translatePullbackLift α β t ≫ hc9k_diff α β =
      toUnit (hc9k_translatePullbackOver α β t) ≫ t := by
  have := hc9k_inv_mul_of_mulRight
    ((Over.homMk (pullback.fst _ _) rfl : hc9k_translatePullbackOver α β t ⟶ A) ≫ α)
    ((Over.homMk (pullback.snd _ _) (hc9k_translatePullback_snd_hom α β t) :
      hc9k_translatePullbackOver α β t ⟶ B) ≫ β) t (by
      ext
      simp only [Over.comp_left, Over.homMk_left, Category.assoc]
      exact pullback.condition)
  rw [← this, hc9k_translatePullbackLift, hc9k_diff, ← Category.assoc, comp_lift,
    Limits.prod.lift_fst_assoc, Limits.prod.lift_snd_assoc, Category.assoc]

/-- The map from the fibre of the difference map to the translated-coordinate pullback. -/
def hc9k_diffFiberToPullback [LocallyOfFiniteType X.hom] :
    (hc9k_diff α β).left.fiber t.underlying ⟶
      pullback (α.left ≫ (GrpObj.mulRight t).hom.left) β.left :=
  pullback.lift ((hc9k_diff α β).left.fiberι t.underlying ≫ (Limits.prod.fst : A ⨯ B ⟶ A).left)
    ((hc9k_diff α β).left.fiberι t.underlying ≫ (Limits.prod.snd : A ⨯ B ⟶ B).left)
    (by simpa only [Category.assoc] using hc9k_diff_fiber_condition α β t)

/-- The map from the translated-coordinate pullback to the fibre of the difference map. -/
def hc9k_pullbackToDiffFiber [LocallyOfFiniteType X.hom] :
    pullback (α.left ≫ (GrpObj.mulRight t).hom.left) β.left ⟶
      (hc9k_diff α β).left.fiber t.underlying :=
  pullback.lift (hc9k_translatePullbackLift α β t).left
    (pullback.fst _ _ ≫ A.hom ≫
      Spec.map (residueFieldIsoBase X.hom _ (hc9k_isClosed_underlying t)).hom) (by
      have h := congrArg Over.Hom.left (hc9k_translatePullbackLift_diff α β t)
      have h1 : (toUnit (hc9k_translatePullbackOver α β t)).left =
          pullback.fst _ _ ≫ A.hom := by simp
      rw [Over.comp_left, Over.comp_left, h1] at h
      rw [h, hc9k_fromSpecResidueField_eq, Category.assoc, Category.assoc, Category.assoc,
        ← Category.assoc (Spec.map (residueFieldIsoBase X.hom _ _).hom), ← Spec.map_comp,
        Iso.inv_hom_id, Spec.map_id, Category.id_comp])

/-- Maps into a scheme-theoretic fibre are determined by their two components. -/
theorem hc9k_fiber_ext {Y Z W : Scheme} {f : Y ⟶ Z} {z : Z} (g h : W ⟶ f.fiber z)
    (h₁ : g ≫ f.fiberι z = h ≫ f.fiberι z)
    (h₂ : g ≫ f.fiberToSpecResidueField z = h ≫ f.fiberToSpecResidueField z) : g = h :=
  pullback.hom_ext h₁ h₂

omit [GrpObj X] in
/-- Maps into a product of schemes over `Spec ℂ` are determined by their two coordinates. -/
theorem hc9k_prod_left_ext {W : Scheme} (g h : W ⟶ (A ⨯ B).left)
    (h₁ : g ≫ (Limits.prod.fst : A ⨯ B ⟶ A).left = h ≫ (Limits.prod.fst : A ⨯ B ⟶ A).left)
    (h₂ : g ≫ (Limits.prod.snd : A ⨯ B ⟶ B).left = h ≫ (Limits.prod.snd : A ⨯ B ⟶ B).left) :
    g = h := by
  have hs : g ≫ (A ⨯ B).hom = h ≫ (A ⨯ B).hom := by
    rw [← Over.w (Limits.prod.fst : A ⨯ B ⟶ A), reassoc_of% h₁]
  have := Limits.prod.hom_ext
    (f := (Over.homMk g hs : Over.mk (h ≫ (A ⨯ B).hom) ⟶ A ⨯ B)) (g := Over.homMk h rfl)
    (by ext; exact h₁) (by ext; exact h₂)
  exact congrArg Over.Hom.left this

/-- First component of `hc9k_diffFiberToPullback`. -/
@[reassoc (attr := simp)]
theorem hc9k_diffFiberToPullback_fst [LocallyOfFiniteType X.hom] :
    hc9k_diffFiberToPullback α β t ≫ pullback.fst _ _ =
      (hc9k_diff α β).left.fiberι t.underlying ≫ (Limits.prod.fst : A ⨯ B ⟶ A).left :=
  pullback.lift_fst _ _ _

/-- Second component of `hc9k_diffFiberToPullback`. -/
@[reassoc (attr := simp)]
theorem hc9k_diffFiberToPullback_snd [LocallyOfFiniteType X.hom] :
    hc9k_diffFiberToPullback α β t ≫ pullback.snd _ _ =
      (hc9k_diff α β).left.fiberι t.underlying ≫ (Limits.prod.snd : A ⨯ B ⟶ B).left :=
  pullback.lift_snd _ _ _

/-- Source component of `hc9k_pullbackToDiffFiber`. -/
@[reassoc (attr := simp)]
theorem hc9k_pullbackToDiffFiber_fiberι [LocallyOfFiniteType X.hom] :
    hc9k_pullbackToDiffFiber α β t ≫ (hc9k_diff α β).left.fiberι t.underlying =
      (hc9k_translatePullbackLift α β t).left :=
  pullback.lift_fst _ _ _

/-- Residue-field component of `hc9k_pullbackToDiffFiber`. -/
@[reassoc (attr := simp)]
theorem hc9k_pullbackToDiffFiber_toSpec [LocallyOfFiniteType X.hom] :
    hc9k_pullbackToDiffFiber α β t ≫ (hc9k_diff α β).left.fiberToSpecResidueField t.underlying =
      pullback.fst _ _ ≫ A.hom ≫
        Spec.map (residueFieldIsoBase X.hom _ (hc9k_isClosed_underlying t)).hom :=
  pullback.lift_snd _ _ _

/-- The fibre of the difference map over `t` is the pullback of `β` along `α` followed by
right translation by `t`. -/
def hc9k_diffFiberIso [LocallyOfFiniteType X.hom] :
    (hc9k_diff α β).left.fiber t.underlying ≅
      pullback (α.left ≫ (GrpObj.mulRight t).hom.left) β.left where
  hom := hc9k_diffFiberToPullback α β t
  inv := hc9k_pullbackToDiffFiber α β t
  hom_inv_id := by
    apply hc9k_fiber_ext
    · rw [Category.assoc, hc9k_pullbackToDiffFiber_fiberι, Category.id_comp]
      apply hc9k_prod_left_ext
      · rw [Category.assoc, hc9k_translatePullbackLift_fst, hc9k_diffFiberToPullback_fst]
      · rw [Category.assoc, hc9k_translatePullbackLift_snd, hc9k_diffFiberToPullback_snd]
    · rw [Category.assoc, hc9k_pullbackToDiffFiber_toSpec, Category.id_comp,
        ← cancel_mono (Spec.map (residueFieldIsoBase X.hom _ (hc9k_isClosed_underlying t)).inv)]
      simp only [Category.assoc]
      rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id,
        SpecMap_residueFieldIsoBase_inv, ← Scheme.Hom.fiber_fac_assoc,
        hc9k_diffFiberToPullback_fst_assoc, Over.w, Over.w]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, hc9k_diffFiberToPullback_fst, hc9k_pullbackToDiffFiber_fiberι_assoc,
        hc9k_translatePullbackLift_fst, Category.id_comp]
    · rw [Category.assoc, hc9k_diffFiberToPullback_snd, hc9k_pullbackToDiffFiber_fiberι_assoc,
        hc9k_translatePullbackLift_snd, Category.id_comp]

end Fibre


section Intersection

variable {G Z₁ Z₂ : Scheme} (i : Z₁ ⟶ G) (j : Z₂ ⟶ G) [IsClosedImmersion i]
  [IsClosedImmersion j] (m : G ⟶ G) (I J : G.IdealSheafData) (hI : i.ker = I)
  (hJ : j.ker.comap m = J)

omit [IsClosedImmersion i] [IsClosedImmersion j] in
include hI hJ in
/-- The ideal sum lies in the kernel of the translated-coordinate pullback. -/
theorem hc9k_sup_le_ker_fst :
    (I ⊔ J).subschemeι.ker ≤ (pullback.fst (i ≫ m) j ≫ i).ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, ← hI, sup_le_iff]
  refine ⟨Scheme.Hom.le_ker_comp _ _, ?_⟩
  rw [← hJ, ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker,
    Category.assoc, pullback.condition]
  exact Scheme.Hom.le_ker_comp _ _

omit [IsClosedImmersion i] [IsClosedImmersion j] in
include hI in
/-- The first kernel lies in the ideal sum. -/
theorem hc9k_le_ker_sup_left : i.ker ≤ (I ⊔ J).subschemeι.ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, hI]
  exact le_sup_left

omit [IsClosedImmersion i] [IsClosedImmersion j] in
include hJ in
/-- The second kernel lies in the kernel of the translated ideal-sum inclusion. -/
theorem hc9k_le_ker_sup_right : j.ker ≤ ((I ⊔ J).subschemeι ≫ m).ker := by
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.le_map_iff_comap_le, hJ,
    Scheme.IdealSheafData.ker_subschemeι]
  exact le_sup_right

/-- The pullback of a closed immersion along another one followed by `m` is the closed
subscheme of the sum of the first kernel and the pulled-back second kernel. -/
def hc9k_pullbackSupIso : pullback (i ≫ m) j ≅ (I ⊔ J).subscheme where
  hom := IsClosedImmersion.lift _ _ (hc9k_sup_le_ker_fst i j m I J hI hJ)
  inv := pullback.lift (IsClosedImmersion.lift i _ (hc9k_le_ker_sup_left i I J hI))
    (IsClosedImmersion.lift j _ (hc9k_le_ker_sup_right j m I J hJ)) (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [← cancel_mono i]
      simp
    · rw [← cancel_mono j]
      simp [pullback.condition]
  inv_hom_id := by
    rw [← cancel_mono (I ⊔ J).subschemeι]
    simp

/-- `hc9k_pullbackSupIso` is compatible with the inclusions into `G`. -/
@[reassoc (attr := simp)]
theorem hc9k_pullbackSupIso_hom_ι :
    (hc9k_pullbackSupIso i j m I J hI hJ).hom ≫ (I ⊔ J).subschemeι = pullback.fst _ _ ≫ i :=
  IsClosedImmersion.lift_fac _ _ _

end Intersection

end Hc9kFibre

section Hc9kSmooth

variable {G Z₂ S : Scheme} (j : Z₂ ⟶ G) [IsClosedImmersion j] (m : G ≅ G)
  (J : G.IdealSheafData) (hJ : j.ker.comap m.hom = J)

omit [IsClosedImmersion j] in
include hJ in
/-- The subscheme cut out by the pulled-back kernel maps to the original one. -/
theorem hc9k_le_ker_translate_hom : j.ker ≤ (J.subschemeι ≫ m.hom).ker := by
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.le_map_iff_comap_le, hJ,
    Scheme.IdealSheafData.ker_subschemeι]

omit [IsClosedImmersion j] in
include hJ in
/-- The original closed subscheme maps back to the one cut out by the pulled-back kernel. -/
theorem hc9k_le_ker_translate_inv : J.subschemeι.ker ≤ (j ≫ m.inv).ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, ← hJ, ← Scheme.IdealSheafData.le_map_iff_comap_le,
    Scheme.IdealSheafData.map_ker, Category.assoc, m.inv_hom_id, Category.comp_id]

/-- Translating a closed subscheme by an automorphism identifies it with the subscheme of the
pulled-back kernel. -/
def hc9k_translateSubschemeIso : J.subscheme ≅ Z₂ where
  hom := IsClosedImmersion.lift j (J.subschemeι ≫ m.hom) (hc9k_le_ker_translate_hom j m J hJ)
  inv := IsClosedImmersion.lift J.subschemeι (j ≫ m.inv) (hc9k_le_ker_translate_inv j m J hJ)
  hom_inv_id := by
    rw [← cancel_mono J.subschemeι]
    simp
  inv_hom_id := by
    rw [← cancel_mono j]
    simp

/-- Equal morphisms have equal smooth loci. -/
theorem hc9k_smoothLocus_congr {X Y : Scheme} {f g : X ⟶ Y} [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation g] (h : f = g) : f.smoothLocus = g.smoothLocus := by
  subst h
  rfl

omit [IsClosedImmersion j] in
/-- A point lies in the image of the nonsmooth part of a closed immersion exactly when it is the
image of a nonsmooth point. -/
theorem hc9k_mem_image_compl_smoothLocus_iff {Z : Scheme} (i : Z ⟶ G) [IsClosedImmersion i]
    (π : G ⟶ S) [LocallyOfFinitePresentation (i ≫ π)] (a : Z) :
    i a ∈ i '' ((i ≫ π).smoothLocus : Set Z)ᶜ ↔ a ∉ (i ≫ π).smoothLocus := by
  refine ⟨?_, fun h ↦ ⟨a, h, rfl⟩⟩
  rintro ⟨a', ha', he⟩
  rwa [i.isClosedEmbedding.injective he] at ha'

include hJ in
/-- Membership in the translated singular image is detected on any point of the original
closed subscheme over the translate. -/
theorem hc9k_mem_translate_singular_iff (π : G ⟶ S) [LocallyOfFinitePresentation (j ≫ π)]
    [LocallyOfFinitePresentation (J.subschemeι ≫ π)] (hm : m.hom ≫ π = π) (g : G) (b : Z₂)
    (hb : j b = m.hom g) :
    g ∈ J.subschemeι '' ((J.subschemeι ≫ π).smoothLocus : Set J.subscheme)ᶜ ↔
      b ∉ (j ≫ π).smoothLocus := by
  set c := hc9k_translateSubschemeIso j m J hJ
  have hc : c.hom ≫ j = J.subschemeι ≫ m.hom := IsClosedImmersion.lift_fac _ _ _
  have hsm : (J.subschemeι ≫ π).smoothLocus = c.hom ⁻¹ᵁ (j ≫ π).smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    exact hc9k_smoothLocus_congr (by rw [reassoc_of% hc, hm])
  have hcb : c.hom (c.inv b) = b := by
    rw [← Scheme.Hom.comp_apply, c.inv_hom_id]
    simp
  constructor
  · rintro ⟨w, hw, rfl⟩ hbs
    apply hw
    rw [hsm, SetLike.mem_coe, Scheme.Hom.mem_preimage]
    have : j (c.hom w) = j b := by rw [hb, ← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]
    rwa [j.isClosedEmbedding.injective this]
  · intro hbs
    refine ⟨c.inv b, ?_, ?_⟩
    · intro h
      rw [hsm, SetLike.mem_coe, Scheme.Hom.mem_preimage, hcb] at h
      exact hbs h
    · apply m.hom.isOpenEmbedding.injective
      have h := congrArg (fun f ↦ f (c.inv b)) hc
      simp only [Scheme.Hom.comp_apply, hcb] at h
      rw [← hb, h]

end Hc9kSmooth

set_option maxHeartbeats 400000 in
theorem hc9k_actionFiber_iso_intersection_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x y : X.left) (t : ComplexPoint X) :
    ∃ e : (hc9k_actionMap X x y).fiber t.underlying ≅
        (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
      e.hom ≫ (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι =
        (hc9k_actionMap X x y).fiberι t.underlying ≫
          (Limits.prod.fst : hc9k_actionSource X x y ⟶
            Over.mk (cycleComponentι X.left x ≫ X.hom)).left ≫
          cycleComponentι X.left x := by
  let α : Over.mk (cycleComponentι X.left x ≫ X.hom) ⟶ X :=
    Over.homMk (cycleComponentι X.left x) rfl
  let β : Over.mk (cycleComponentι X.left y ≫ X.hom) ⟶ X :=
    Over.homMk (cycleComponentι X.left y) rfl
  have hI : (cycleComponentι X.left x).ker = ccm3_primeIdeal X.left x :=
    Scheme.IdealSheafData.ker_subschemeι _
  have hJ : (cycleComponentι X.left y).ker.comap (GrpObj.mulRight t).hom.left =
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y) := by
    rw [← hc9k_translate_inverseIdeal]
    exact congrArg (Scheme.IdealSheafData.comap · _) (Scheme.IdealSheafData.ker_subschemeι _)
  refine ⟨hc9k_diffFiberIso α β t ≪≫ hc9k_pullbackSupIso (cycleComponentι X.left x) (cycleComponentι X.left y) _ _ _ hI hJ, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg _ (hc9k_pullbackSupIso_hom_ι _ _ _ _ _ hI hJ)).trans
      (hc9k_diffFiberToPullback_fst_assoc α β t _))

theorem hc9k_smooth_fiber_gives_transverse_off_singular_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x y : X.left) (t : ComplexPoint X) :
    Smooth ((hc9k_regularActionMap X x y).fiberToSpecResidueField t.underlying) →
      ∀ v : (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
        (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v ∉
            (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) →
        (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v ∉
            (cycleComponentSingularAmbientClosedFiltration X
              (hc9k_translatePoint X t y) 0 : Set X.left) →
          v ∈ ((ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι ≫
              X.hom).smoothLocus := by
  intro hsmooth v hv₁ hv₂
  let z := hc9k_translatePoint X t y
  let I := ccm3_primeIdeal X.left x
  let J := ccm3_primeIdeal X.left z
  let a := cycleComponentι X.left x
  let b := cycleComponentι X.left y
  let mI : X.left ≅ X.left := (Over.forget _).mapIso (GrpObj.mulRight t)
  let sx := (a ≫ X.hom).smoothLocus
  let sy := (b ≫ X.hom).smoothLocus
  let αr : Over.mk (sx.ι ≫ a ≫ X.hom) ⟶ X := Over.homMk (sx.ι ≫ a) rfl
  let βr : Over.mk (sy.ι ≫ b ≫ X.hom) ⟶ X := Over.homMk (sy.ι ≫ b) rfl
  have hI : a.ker = I := Scheme.IdealSheafData.ker_subschemeι _
  have hJ : b.ker.comap mI.hom = J :=
    (congrArg (Scheme.IdealSheafData.comap · _) (Scheme.IdealSheafData.ker_subschemeι _)).trans
      (hc9k_translate_inverseIdeal X t y)
  let ιT := (I ⊔ J).subschemeι
  let e := hc9k_pullbackSupIso a b mI.hom I J hI hJ
  -- the regular pullback is smooth over `Spec ℂ`
  have hP : Smooth (pullback.fst ((sx.ι ≫ a) ≫ mI.hom) (sy.ι ≫ b) ≫ sx.ι ≫ a ≫ X.hom) := by
    have h := hc9k_pullbackToDiffFiber_toSpec αr βr t
    have hE : pullback.fst ((sx.ι ≫ a) ≫ mI.hom) (sy.ι ≫ b) ≫ sx.ι ≫ a ≫ X.hom =
        (hc9k_diffFiberIso αr βr t).inv ≫
          (hc9k_diff αr βr).left.fiberToSpecResidueField t.underlying ≫
            Spec.map (residueFieldIsoBase X.hom _ (hc9k_isClosed_underlying t)).inv := by
      change _ = hc9k_pullbackToDiffFiber αr βr t ≫ _
      rw [reassoc_of% h, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
      rfl
    have h₁ : Smooth ((hc9k_diff αr βr).left.fiberToSpecResidueField t.underlying) := hsmooth
    have h₂ : Smooth (hc9k_diffFiberIso αr βr t).inv := inferInstance
    have h₃ : Smooth (Spec.map (residueFieldIsoBase X.hom _ (hc9k_isClosed_underlying t)).inv) :=
      inferInstance
    rw [hE]
    exact @smooth_comp _ _ _ _ _ h₂ (@smooth_comp _ _ _ _ _ h₁ h₃)
  -- the two singular images, detected on the component closures
  let S₁ := (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left)
  let S₂ := (cycleComponentSingularAmbientClosedFiltration X z 0 : Set X.left)
  have hS₁ (p : cycleComponent X.left x) : a p ∈ S₁ ↔ p ∉ sx :=
    hc9k_mem_image_compl_smoothLocus_iff a X.hom p
  have hS₂ (g : X.left) (p : cycleComponent X.left y) (hp : b p = mI.hom g) :
      g ∈ S₂ ↔ p ∉ sy :=
    hc9k_mem_translate_singular_iff b mI J hJ X.hom (Over.w (GrpObj.mulRight t).hom) g p hp
  let U : (I ⊔ J).subscheme.Opens :=
    ⟨ιT ⁻¹' (S₁ ∪ S₂)ᶜ, ((cycleComponentSingularAmbientClosedFiltration X x 0).isClosed.union
      (cycleComponentSingularAmbientClosedFiltration X z 0).isClosed).isOpen_compl.preimage
        ιT.continuous⟩
  have hq₁ : e.inv ≫ pullback.fst _ _ ≫ a = ιT := by
    rw [← hc9k_pullbackSupIso_hom_ι a b mI.hom I J hI hJ, Iso.inv_hom_id_assoc]
  have hq₂ : e.inv ≫ pullback.snd _ _ ≫ b = ιT ≫ mI.hom := by
    rw [← pullback.condition, reassoc_of% hq₁]
  have hU₁ : Set.range (U.ι ≫ e.inv ≫ pullback.fst _ _) ⊆ Set.range sx.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    by_contra hn
    have hu : U.ι u ∈ U := u.2
    apply hu
    left
    have := (hS₁ _).2 hn
    rwa [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hq₁] at this
  have hU₂ : Set.range (U.ι ≫ e.inv ≫ pullback.snd _ _) ⊆ Set.range sy.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    by_contra hn
    have hu : U.ι u ∈ U := u.2
    apply hu
    right
    refine (hS₂ _ _ ?_).2 hn
    rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hq₂, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
  -- the open part of the intersection is the regular pullback
  let gA := IsOpenImmersion.lift sx.ι _ hU₁
  let gB := IsOpenImmersion.lift sy.ι _ hU₂
  have hgAB : gA ≫ (sx.ι ≫ a) ≫ mI.hom = gB ≫ sy.ι ≫ b := by
    simp only [gA, gB, Category.assoc, IsOpenImmersion.lift_fac_assoc, pullback.condition]
  let g : U.toScheme ⟶ pullback ((sx.ι ≫ a) ≫ mI.hom) (sy.ι ≫ b) := pullback.lift gA gB hgAB
  have hg : g ≫ pullback.fst _ _ ≫ sx.ι ≫ a = U.ι ≫ ιT := by
    simp only [g, gA, pullback.lift_fst_assoc, IsOpenImmersion.lift_fac_assoc, Category.assoc,
      hq₁]
  let k : pullback ((sx.ι ≫ a) ≫ mI.hom) (sy.ι ≫ b) ⟶ (I ⊔ J).subscheme :=
    pullback.map _ _ _ _ sx.ι sy.ι (𝟙 _) (by simp) (by simp) ≫ e.hom
  have hk : k ≫ ιT = pullback.fst _ _ ≫ sx.ι ≫ a := by
    simp only [k, ιT, e, Category.assoc, hc9k_pullbackSupIso_hom_ι, pullback.lift_fst_assoc]
  have hU₃ : Set.range k ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hp : ιT (k p) = a (sx.ι (pullback.fst ((sx.ι ≫ a) ≫ mI.hom) (sy.ι ≫ b) p)) := by
      rw [← Scheme.Hom.comp_apply, hk, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    rintro (h | h)
    · rw [hp, hS₁] at h
      exact h ((Scheme.Opens.range_ι sx).subset ⟨_, rfl⟩)
    · refine (hS₂ _ (sy.ι (pullback.snd ((sx.ι ≫ a) ≫ mI.hom) (sy.ι ≫ b) p)) ?_).1 h
        ((Scheme.Opens.range_ι sy).subset ⟨_, rfl⟩)
      have := congrArg (fun f ↦ f p)
        (pullback.condition (f := (sx.ι ≫ a) ≫ mI.hom) (g := sy.ι ≫ b))
      simp only [Scheme.Hom.comp_apply] at this
      rw [hp, ← this]
  let gi : pullback ((sx.ι ≫ a) ≫ mI.hom) (sy.ι ≫ b) ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι k hU₃
  have hgi : gi ≫ U.ι ≫ ιT = pullback.fst _ _ ≫ sx.ι ≫ a := by
    rw [IsOpenImmersion.lift_fac_assoc, hk]
  let gIso : U.toScheme ≅ pullback ((sx.ι ≫ a) ≫ mI.hom) (sy.ι ≫ b) :=
    { hom := g
      inv := gi
      hom_inv_id := by
        rw [← cancel_mono (U.ι ≫ ιT), Category.assoc, hgi, hg, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [← cancel_mono (sx.ι ≫ a)]
          simp only [Category.assoc, Category.id_comp]
          rw [hg, hgi]
        · rw [← cancel_mono (sy.ι ≫ b)]
          simp only [Category.assoc, Category.id_comp]
          rw [← pullback.condition]
          simp only [Category.assoc]
          rw [reassoc_of% hg, reassoc_of% hgi] }
  -- smoothness on `U`
  have hU : Smooth (U.ι ≫ ιT ≫ X.hom) := by
    have : U.ι ≫ ιT ≫ X.hom =
        gIso.hom ≫ pullback.fst ((sx.ι ≫ a) ≫ mI.hom) (sy.ι ≫ b) ≫ sx.ι ≫ a ≫ X.hom := by
      change _ = g ≫ _
      rw [reassoc_of% hg]
    rw [this]
    have : IsIso gIso.hom := Iso.isIso_hom gIso
    have : Smooth gIso.hom := inferInstance
    exact @smooth_comp _ _ _ _ _ this hP
  have hvU : v ∈ U := fun h ↦ h.elim hv₁ hv₂
  have h := Scheme.Hom.preimage_smoothLocus_eq U.ι (ιT ≫ X.hom)
  rw [Scheme.Hom.smoothLocus_eq_top (U.ι ≫ ιT ≫ X.hom)] at h
  have : (⟨v, hvU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ (ιT ≫ X.hom).smoothLocus := by
    rw [h]
    trivial
  exact this

theorem hc9k_genericFiber_expected_coheight_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    ∃ V : X.left.Opens, Dense (V : Set X.left) ∧
      ∀ t : ComplexPoint X, t.underlying ∈ V → ∀ w : (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
        closure ({w} : Set _) ∈ irreducibleComponents
            (ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme →
          Order.coheight ((ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w) =
              Order.coheight x + Order.coheight y :=
  hc9k8_expected_coheight X x y fun t =>
    ⟨(hc9k_actionFiber_iso_intersection_aux X x y t).choose⟩

/-- One factor of the regular difference-map source: the smooth locus of a component closure. -/
private abbrev hc9k_regularFactor (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) : Over (Spec ↧ℂ) :=
  Over.mk ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫ cycleComponentι X.left x ≫ X.hom)

private instance hc9k_regularFactor_smooth (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Smooth (hc9k_regularFactor X x).hom :=
  Scheme.Hom.smooth_restrict_smoothLocus _

private instance hc9k_regularFactor_locallyOfFiniteType (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    LocallyOfFiniteType (hc9k_regularFactor X x).hom := by
  dsimp [hc9k_regularFactor]; infer_instance

private instance hc9k_regularFactor_quasiCompact (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    QuasiCompact (hc9k_regularFactor X x).hom := by
  have := cycleComponent_isNoetherian X x
  dsimp [hc9k_regularFactor]; infer_instance

private instance hc9k_regularFactor_isIntegral (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    IsIntegral (hc9k_regularFactor X x).left := by
  obtain ⟨y, hy⟩ := (dense_cycleComponent_smoothLocus X x).nonempty
  have : Nonempty (hc9k_regularFactor X x).left := ⟨⟨y, hy⟩⟩
  exact isIntegral_of_isOpenImmersion (cycleComponentι X.left x ≫ X.hom).smoothLocus.ι

/-- The product of two integral regular loci over `ℂ` is integral. -/
private instance hc9k_regularActionSource_isIntegral (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    IsIntegral (hc9k_regularActionSource X x y).left := by
  have := HodgeLean.Foundations.isIntegral_pullback_of_isAlgClosed ℂ _ _
    (hc9k_regularFactor X x).hom (hc9k_regularFactor X y).hom
  have : Nonempty (hc9k_regularActionSource X x y).left :=
    ⟨(Over.prodLeftIsoPullback (hc9k_regularFactor X x) (hc9k_regularFactor X y)).inv
      (Classical.choice inferInstance)⟩
  exact isIntegral_of_isOpenImmersion
    (Over.prodLeftIsoPullback (hc9k_regularFactor X x) (hc9k_regularFactor X y)).hom

private lemma hc9k_regularActionSource_hom (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    (hc9k_regularActionSource X x y).hom =
      (Over.prodLeftIsoPullback (hc9k_regularFactor X x) (hc9k_regularFactor X y)).hom ≫
        pullback.fst _ _ ≫ (hc9k_regularFactor X x).hom := by
  rw [Over.prodLeftIsoPullback_hom_fst_assoc, Over.w]

/-- The product of two regular loci is smooth over `ℂ`. -/
private instance hc9k_regularActionSource_smooth (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    Smooth (hc9k_regularActionSource X x y).hom := by
  rw [hc9k_regularActionSource_hom]; infer_instance

private instance hc9k_regularActionSource_quasiCompact (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    QuasiCompact (hc9k_regularActionSource X x y).hom := by
  rw [hc9k_regularActionSource_hom]; infer_instance

private instance hc9k_regularActionSource_locallyOfFiniteType (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    LocallyOfFiniteType (hc9k_regularActionSource X x y).hom := by
  rw [hc9k_regularActionSource_hom]; infer_instance

/-- The regular difference map is locally of finite presentation. -/
private instance hc9k_regularActionMap_locallyOfFinitePresentation (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    LocallyOfFinitePresentation (hc9k_regularActionMap X x y) := by
  have hf : hc9k_regularActionMap X x y ≫ X.hom = (hc9k_regularActionSource X x y).hom :=
    Over.w _
  have : LocallyOfFiniteType (hc9k_regularActionMap X x y ≫ X.hom) := by
    rw [hf]; infer_instance
  have := locallyOfFiniteType_of_comp (hc9k_regularActionMap X x y) X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

/-- The regular difference map is quasi-compact. -/
private instance hc9k_regularActionMap_quasiCompact (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    QuasiCompact (hc9k_regularActionMap X x y) := by
  have hf : hc9k_regularActionMap X x y ≫ X.hom = (hc9k_regularActionSource X x y).hom :=
    Over.w _
  have : QuasiCompact (hc9k_regularActionMap X x y ≫ X.hom) := by
    rw [hf]; infer_instance
  exact QuasiCompact.of_comp (hc9k_regularActionMap X x y) X.hom

/-- Smoothness over an open of the target gives smooth fibres over its points. -/
private lemma hc9k_smooth_fiber_of_smooth_restrict {S Y : Scheme} (f : S ⟶ Y) (U : Y.Opens)
    [Smooth (f ∣_ U)] (y : Y) (hy : y ∈ U) :
    Smooth (f.fiberToSpecResidueField y) := by
  let g : Spec (Y.residueField y) ⟶ U := IsOpenImmersion.lift U.ι (Y.fromSpecResidueField y)
    (by rw [Scheme.range_fromSpecResidueField]; simpa using hy)
  have hg : g ≫ U.ι = Y.fromSpecResidueField y := IsOpenImmersion.lift_fac _ _ _
  have hP : IsPullback (pullback.fst (f ∣_ U) g ≫ (f ⁻¹ᵁ U).ι) (pullback.snd (f ∣_ U) g) f
      (Y.fromSpecResidueField y) := by
    rw [← hg]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (isPullback_morphismRestrict f U).flip
  have : f.fiberToSpecResidueField y = hP.isoPullback.inv ≫ pullback.snd (f ∣_ U) g :=
    hP.isoPullback_inv_snd.symm
  rw [this]
  have h1 : Smooth (pullback.snd (f ∣_ U) g) := inferInstance
  have h2 : Smooth hP.isoPullback.inv := inferInstance
  exact MorphismProperty.comp_mem _ _ _ h2 h1

/-- The fibre over a point outside the image is empty, hence smooth. -/
private lemma hc9k_smooth_fiber_of_not_mem_range {S Y : Scheme} (f : S ⟶ Y)
    [LocallyOfFinitePresentation f] (y : Y) (hy : y ∉ Set.range f) :
    Smooth (f.fiberToSpecResidueField y) := by
  have : IsEmpty (f.fiber y) := ⟨fun z ↦ hy ⟨f.fiberι y z, (f.range_fiberι y).subset ⟨z, rfl⟩⟩⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  ext z
  exact isEmptyElim z

/-- The dominant/non-dominant split for a map from a smooth integral source to `X.left`. -/
private lemma hc9k_dense_open_smooth_fibers (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] {S : Scheme} (sS : S ⟶ Spec ↧ℂ) (f : S ⟶ X.left) [IsIntegral S]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [LocallyOfFiniteType sS] [Smooth sS]
    (hf : f ≫ X.hom = sS) :
    ∃ V : X.left.Opens, Dense (V : Set X.left) ∧
      ∀ v ∈ V, Smooth (f.fiberToSpecResidueField v) := by
  by_cases hd : IsDominant f
  · obtain ⟨U, hU, hsm⟩ := gfs_exists_smooth_over_dense_open sS X.hom f hf
    exact ⟨U, hU, fun v hv ↦ hc9k_smooth_fiber_of_smooth_restrict f U v hv⟩
  · have hne : closure (Set.range f) ≠ Set.univ := fun h ↦
      hd ⟨dense_iff_closure_eq.mpr h⟩
    refine ⟨⟨(closure (Set.range f))ᶜ, isClosed_closure.isOpen_compl⟩,
      isClosed_closure.isOpen_compl.dense (Set.nonempty_compl.mpr hne),
      fun v hv ↦ hc9k_smooth_fiber_of_not_mem_range f v fun h ↦ hv (subset_closure h)⟩

theorem hc9k_regular_intersection_generically_transverse_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    ∃ V : X.left.Opens, Dense (V : Set X.left) ∧
      ∀ t : ComplexPoint X, t.underlying ∈ V →
        Smooth ((hc9k_regularActionMap X x y).fiberToSpecResidueField t.underlying) := by
  obtain ⟨V, hV, hsm⟩ := hc9k_dense_open_smooth_fibers X (hc9k_regularActionSource X x y).hom
    (hc9k_regularActionMap X x y) (Over.w _)
  exact ⟨V, hV, fun t ht ↦ hsm _ ht⟩

/-- Every point of a closed set lies in the closure of one of finitely many of its points.
Source: Hartshorne, *Algebraic Geometry*, I.1.5 and II.2.9; Mathlib
`NoetherianSpace.exists_finite_set_isClosed_irreducible`. -/
private theorem hc9k_d_closed_finite_generic (Y : Scheme) [NoetherianSpace Y] (C : Closeds Y) :
    ∃ F : Set Y, F.Finite ∧ (∀ s ∈ F, s ∈ C) ∧
      ∀ p ∈ C, ∃ s ∈ F, p ∈ closure ({s} : Set Y) := by
  obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible C.isClosed
  refine ⟨{s | ∃ T ∈ S, IsGenericPoint s T}, ?_, ?_, ?_⟩
  · have : {s | ∃ T ∈ S, IsGenericPoint s T} = ⋃ T ∈ S, {s | IsGenericPoint s T} := by
      ext s; simp
    rw [this]
    exact hSf.biUnion fun T _ => Set.Subsingleton.finite fun a ha b hb => ha.eq hb
  · rintro s ⟨T, hT, hs⟩
    change s ∈ (C : Set Y)
    rw [hS]
    exact ⟨T, hT, hs.mem⟩
  · intro p hp
    change p ∈ (C : Set Y) at hp
    rw [hS] at hp
    obtain ⟨T, hT, hpT⟩ := hp
    obtain ⟨s, hs⟩ := QuasiSober.sober (hSi T hT) (hSc T hT)
    exact ⟨s, ⟨T, hT, hs⟩, by rw [hs.def]; exact hpT⟩

/-- Finitely many dense opens contain a common dense open.
Source: Bourbaki, *General Topology*, I.1.6, Proposition 5. -/
private theorem hc9k_d_dense_finite_inter {Y : Type*} [TopologicalSpace Y] {ι : Type*}
    {F : Set ι} (hF : F.Finite) (V : ι → Opens Y) (hV : ∀ i, Dense (V i : Set Y)) :
    ∃ W : Opens Y, Dense (W : Set Y) ∧ ∀ i ∈ F, W ≤ V i := by
  classical
  lift F to Finset ι using hF
  induction F using Finset.induction_on with
  | empty => exact ⟨⊤, by simp, by simp⟩
  | insert a F _ ih =>
    obtain ⟨W, hWd, hW⟩ := ih
    refine ⟨V a ⊓ W, (hV a).inter_of_isOpen_left hWd (V a).isOpen, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact inf_le_left
    · exact inf_le_right.trans (hW i hi)

/-- On the dense open of step 8, every point of the translated intersection has coheight at
least the expected component coheight.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), Theorem 2(i); Hartshorne, *Algebraic Geometry*, II.3. -/
private theorem hc9k_d_coheight_le_of_mem
    (X : Over (Spec ↧ℂ)) [GrpObj X] (a b : X.left) (V : X.left.Opens)
    (hV : ∀ t : ComplexPoint X, t.underlying ∈ V → ∀ w : (ccm3_primeIdeal X.left a ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t b)).subscheme,
        closure ({w} : Set _) ∈ irreducibleComponents
            (ccm3_primeIdeal X.left a ⊔
              ccm3_primeIdeal X.left (hc9k_translatePoint X t b)).subscheme →
          Order.coheight ((ccm3_primeIdeal X.left a ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t b)).subschemeι w) =
              Order.coheight a + Order.coheight b)
    (t : ComplexPoint X) (ht : t.underlying ∈ V) (p : X.left)
    (hpa : p ∈ closure ({a} : Set X.left))
    (hpb : p ∈ closure ({hc9k_translatePoint X t b} : Set X.left)) :
    Order.coheight a + Order.coheight b ≤ Order.coheight p := by
  let I := ccm3_primeIdeal X.left a ⊔ ccm3_primeIdeal X.left (hc9k_translatePoint X t b)
  have hp : p ∈ (I.support : Set X.left) := by
    simp only [I, Scheme.IdealSheafData.support_sup, Closeds.coe_inf, ccm3_primeIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact ⟨hpa, hpb⟩
  let v : I.subscheme := ⟨p, hp⟩
  have hC := irreducibleComponent_mem_irreducibleComponents v
  obtain ⟨w, hw⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
  have h1 := hV t ht w (by rw [hw.def]; exact hC)
  have hv : v ∈ closure ({w} : Set I.subscheme) := by
    rw [hw.def]; exact mem_irreducibleComponent
  have hsp : I.subschemeι w ⤳ I.subschemeι v :=
    (specializes_iff_mem_closure.mpr hv).map I.subschemeι.continuous
  rw [← h1]
  exact Order.coheight_anti (Scheme.le_iff_specializes.mpr hsp)

/-- A point of the singular boundary of a translated component translates back into the
singular boundary of the original component.
Source: Stacks Project, Tag 01V4 (smoothness is invariant under isomorphism); Mathlib
`GrpObj.mulRight`. -/
private theorem hc9k_d_singular_translate
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (t : ComplexPoint X) (y p : X.left)
    (hp : p ∈ cycleComponentSingularAmbientClosedFiltration X
      (hc9k_translatePoint X t y) 0) :
    (GrpObj.mulRight t).hom.left p ∈ cycleComponentSingularAmbientClosedFiltration X y 0 := by
  let ψ := (GrpObj.mulRight t).hom.left
  have hI : (ccm3_primeIdeal X.left y).comap ψ =
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y) :=
    hc9k_translate_inverseIdeal_aux X t y
  have hg : ∃ g : cycleComponent X.left (hc9k_translatePoint X t y) ⟶
      cycleComponent X.left y, IsIso g ∧
        g ≫ cycleComponentι X.left y =
          cycleComponentι X.left (hc9k_translatePoint X t y) ≫ ψ := by
    change ∃ g : (ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme ⟶
      (ccm3_primeIdeal X.left y).subscheme, IsIso g ∧
        g ≫ (ccm3_primeIdeal X.left y).subschemeι =
          (ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι ≫ ψ
    rw [← hI]
    refine ⟨((ccm3_primeIdeal X.left y).comapIso ψ).hom ≫ pullback.snd _ _,
      inferInstance, ?_⟩
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  obtain ⟨g, hgi, hgc⟩ := hg
  obtain ⟨a, ha, rfl⟩ := hp
  refine ⟨g a, fun hs => ha ?_, ?_⟩
  · have hw : ψ ≫ X.hom = X.hom := Over.w (GrpObj.mulRight t).hom
    have hm : a ∈ g ⁻¹ᵁ (cycleComponentι X.left y ≫ X.hom).smoothLocus := hs
    rw [Scheme.Hom.preimage_smoothLocus_eq] at hm
    have he : g ≫ cycleComponentι X.left y ≫ X.hom =
        cycleComponentι X.left (hc9k_translatePoint X t y) ≫ X.hom := by
      rw [← Category.assoc, hgc, Category.assoc, hw]
    simp only [he] at hm
    exact hm
  · exact (Scheme.Hom.comp_apply _ _ a).symm.trans (congrArg (fun k => k a) hgc) |>.trans
      (Scheme.Hom.comp_apply _ _ a)

theorem hc9k_singular_intersections_smaller_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    ∃ V : X.left.Opens, Dense (V : Set X.left) ∧
      ∀ t : ComplexPoint X, t.underlying ∈ V →
      (∀ v : (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
        (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v ∈
            (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) →
          Order.coheight x + Order.coheight y <
            Order.coheight ((ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v)) ∧
      (∀ v : (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
        (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v ∈
            (cycleComponentSingularAmbientClosedFiltration X
              (hc9k_translatePoint X t y) 0 : Set X.left) →
          Order.coheight x + Order.coheight y <
            Order.coheight ((ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v)) := by
  classical
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := { }
  have hfin (u : X.left) : Order.coheight u = ((Order.coheight u).toNat : ℕ∞) :=
    (ENat.natCast_toNat (ne_of_lt (lt_of_le_of_lt
      (SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := dim X.left) u)
      (WithTop.coe_lt_top _)))).symm
  have hmem (u w : X.left) (I : X.left.IdealSheafData) (v : I.subscheme)
      (hI : I = ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left w) :
      I.subschemeι v ∈ closure ({u} : Set X.left) ∧
        I.subschemeι v ∈ closure ({w} : Set X.left) := by
    subst hI
    have hv := v.2
    simp only [Scheme.IdealSheafData.support_sup, ccm3_primeIdeal] at hv
    exact hv
  obtain ⟨Fx, hFxf, hFxC, hFx⟩ := hc9k_d_closed_finite_generic X.left
    (cycleComponentSingularAmbientClosedFiltration X x 0)
  obtain ⟨Fy, hFyf, hFyC, hFy⟩ := hc9k_d_closed_finite_generic X.left
    (cycleComponentSingularAmbientClosedFiltration X y 0)
  choose V hVd hV using fun ab : X.left × X.left =>
    hc9k_genericFiber_expected_coheight_aux X ab.1 ab.2
  obtain ⟨W, hWd, hW⟩ := hc9k_d_dense_finite_inter
    ((hFxf.image fun s => (s, y)).union (hFyf.image fun s => (x, s))) V hVd
  refine ⟨W, hWd, fun t ht => ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
  · obtain ⟨s, hsF, hps⟩ := hFx _ hv
    have hle := hc9k_d_coheight_le_of_mem X s y (V (s, y)) (hV (s, y)) t
      (hW (s, y) (Or.inl ⟨s, hsF, rfl⟩) ht) _ hps (hmem _ _ _ v rfl).2
    have hs := ccm5_singularBoundary_coheight_lower_bound X _ x s (hfin x) (hFxC s hsF)
    refine lt_of_lt_of_le ?_ hle
    rw [hfin x, hfin y, hfin s] at *
    have hs' : (Order.coheight x).toNat + 1 ≤ (Order.coheight s).toNat := by exact_mod_cast hs
    exact_mod_cast (by omega)
  · let ψ := (GrpObj.mulRight t).hom.left
    have hψ := hc9k_d_singular_translate X t y _ hv
    obtain ⟨s, hsF, hps⟩ := hFy _ hψ
    have hinv : (GrpObj.mulRight t).inv.left (ψ ((ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v)) =
          (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.hom_inv_id, Over.id_left]
      rfl
    have hpz : (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v ∈
          closure ({hc9k_translatePoint X t s} : Set X.left) := by
      rw [← hinv, ← specializes_iff_mem_closure]
      exact (specializes_iff_mem_closure.mpr hps).map
        (GrpObj.mulRight t).inv.left.continuous
    have hle := hc9k_d_coheight_le_of_mem X x s (V (x, s)) (hV (x, s)) t
      (hW (x, s) (Or.inr ⟨s, hsF, rfl⟩) ht) _ (hmem _ _ _ v rfl).1 hpz
    have hs := ccm5_singularBoundary_coheight_lower_bound X _ y s (hfin y) (hFyC s hsF)
    refine lt_of_lt_of_le ?_ hle
    rw [hfin x, hfin y, hfin s] at *
    have hs' : (Order.coheight y).toNat + 1 ≤ (Order.coheight s).toNat := by exact_mod_cast hs
    exact_mod_cast (by omega)

theorem hc9k_badLocus_strict_coheight_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    ∃ V : X.left.Opens, Dense (V : Set X.left) ∧
      ∀ t : ComplexPoint X, t.underlying ∈ V →
      ∀ v : (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
        (v ∉ ((ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι ≫
              X.hom).smoothLocus ∨
          (ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v ∈
              (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) ∨
          (ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v ∈
              (cycleComponentSingularAmbientClosedFiltration X
                (hc9k_translatePoint X t y) 0 : Set X.left)) →
          Order.coheight x + Order.coheight y <
            Order.coheight ((ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v) := by
  obtain ⟨V₉, hV₉d, hV₉⟩ := hc9k_regular_intersection_generically_transverse_aux X x y
  obtain ⟨V₁₀, hV₁₀d, hV₁₀⟩ := hc9k_singular_intersections_smaller_aux X x y
  refine ⟨V₉ ⊓ V₁₀, hV₉d.inter_of_isOpen_left hV₁₀d V₉.isOpen, fun t ht v hv => ?_⟩
  obtain ⟨hx, hz⟩ := hV₁₀ t ht.2
  by_cases hsx : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v ∈
        (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left)
  · exact hx v hsx
  by_cases hsz : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι v ∈
        (cycleComponentSingularAmbientClosedFiltration X
          (hc9k_translatePoint X t y) 0 : Set X.left)
  · exact hz v hsz
  rcases hv with hns | hv | hv
  · exact (hns (hc9k_smooth_fiber_gives_transverse_off_singular_aux X x y t
      (hV₉ t ht.1) v hsx hsz)).elim
  · exact (hsx hv).elim
  · exact (hsz hv).elim

theorem hc9k_transverseLocus_contains_nonempty_open_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    ∃ V : X.left.Opens, Dense (V : Set X.left) ∧
      ∀ t : ComplexPoint X, t.underlying ∈ V →
        t ∈ hc9k_transverseLocus X x y := by
  obtain ⟨V₁, hV₁, h₁⟩ := hc9k_genericFiber_expected_coheight_aux X x y
  obtain ⟨V₂, hV₂, h₂⟩ := hc9k_regular_intersection_generically_transverse_aux X x y
  refine ⟨V₁ ⊓ V₂, ?_, fun t ht ↦ ⟨h₁ t ht.1,
    hc9k_smooth_fiber_gives_transverse_off_singular_aux X x y t (h₂ t ht.2)⟩⟩
  rw [Opens.coe_inf]
  exact hV₁.inter_of_isOpen_right hV₂ V₂.isOpen

theorem hc9k_transverseLocus_finite_family_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (c d : AlgebraicCycle X.left ℚ) :
    ∃ V : X.left.Opens, Dense (V : Set X.left) ∧
      ∀ t : ComplexPoint X, t.underlying ∈ V →
        ∀ x y, c x ≠ 0 → d y ≠ 0 → t ∈ hc9k_transverseLocus X x y := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  choose U hU hUt using fun p : X.left × X.left ↦
    hc9k_transverseLocus_contains_nonempty_open_aux X p.1 p.2
  let S : Set (X.left × X.left) := Function.support c ×ˢ Function.support d
  have hS : S.Finite := c.finite_support.prod d.finite_support
  let s : Set (Set X.left) := (fun p ↦ (U p : Set X.left)) '' S
  have hs : s.Finite := hS.image _
  have ho : IsOpen (⋂₀ s) := hs.isOpen_sInter (by
    rintro _ ⟨p, -, rfl⟩
    exact (U p).isOpen)
  refine ⟨⟨⋂₀ s, ho⟩, hs.dense_sInter (by
    rintro _ ⟨p, -, rfl⟩
    exact (U p).isOpen) (by
    rintro _ ⟨p, -, rfl⟩
    exact hU p), fun t ht x y hx hy ↦ hUt (x, y) t ?_⟩
  exact Set.mem_sInter.mp ht _ ⟨(x, y), ⟨hx, hy⟩, rfl⟩

end HodgeLean.Adapters

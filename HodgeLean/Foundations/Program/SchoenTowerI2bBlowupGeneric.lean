import HodgeLean.Foundations.Program.SchoenTowerI2bGenericSuppliers

/-! Generic-source control from the retained blowup universal property.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A map avoiding an ideal's support pulls that ideal back to the unit ideal.
Source: support of the inverse-image ideal sheaf. -/
theorem s2v_i2b_comap_eq_top_of_avoids
    {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData)
    (hf : ∀ x : X, f x ∉ I.support) : I.comap f = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  rw [Scheme.IdealSheafData.support_comap] at hx
  exact (hf x hx).elim

/-- The unit pulled-back ideal meets the retained invertibility criterion.
Source: the free rank-one module structure on the unit ideal. -/
theorem s2v_i2b_cartier_of_comap_eq_top
    {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData)
    (hf : I.comap f = ⊤) :
    ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap f).ideal U) ≃ₗ[Γ(X, U.1)] Γ(X, U.1)) := by
  intro x
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top x)
  refine ⟨⟨U, hU⟩, hx, ?_⟩
  refine ⟨(LinearEquiv.ofEq _ _ ?_).trans Submodule.topEquiv⟩
  rw [hf]
  rfl

/-- The retained blowup becomes an isomorphism after any base change avoiding its centre.
Source: the blowup universal property away from the centre. -/
theorem s2v_i2b_blowup_isIso_over_unit_ideal
    {B B' U : Over (Spec ↧ℂ)} (b : B' ⟶ B) (I : B.left.IdealSheafData)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V.1)] Γ(T.left, V.1))) →
      ∃! u : T ⟶ B', u ≫ b = f)
    (ι : U ⟶ B) (hι : I.comap ι.left = ⊤) :
    IsIso (pullback.snd b ι) := by
  obtain ⟨l, hl, -⟩ := hblowup U ι (s2v_i2b_cartier_of_comap_eq_top ι.left I hι)
  let s : U ⟶ pullback b ι := pullback.lift l (𝟙 U) (by simpa only [Category.id_comp] using hl)
  have hs : s ≫ pullback.snd b ι = 𝟙 U := pullback.lift_snd _ _ _
  have hI : I.comap (pullback.fst b ι ≫ b).left = ⊤ := by
    rw [pullback.condition]
    change I.comap ((pullback.snd b ι).left ≫ ι.left) = ⊤
    rw [Scheme.IdealSheafData.comap_comp, hι, Scheme.IdealSheafData.comap_top]
  obtain ⟨a, ha, huniq⟩ := hblowup (pullback b ι) (pullback.fst b ι ≫ b)
    (s2v_i2b_cartier_of_comap_eq_top _ I hI)
  have hlift : pullback.snd b ι ≫ l = pullback.fst b ι := by
    apply (huniq _ ?_).trans (huniq _ rfl).symm
    rw [Category.assoc, hl, pullback.condition]
  refine ⟨⟨s, ?_, hs⟩⟩
  apply pullback.hom_ext
  · change (pullback.snd b ι ≫ s) ≫ pullback.fst b ι = _
    rw [Category.assoc, pullback.lift_fst, hlift, Category.id_comp]
  · change (pullback.snd b ι ≫ s) ≫ pullback.snd b ι = _
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp]

/-- A lift of a dominant map avoiding the centre remains dominant on the integral blowup.
Source: the blowup isomorphism over the complement of the centre and density of nonempty opens. -/
theorem s2v_i2b_blowup_lift_dominant
    {B B' T : Over (Spec ↧ℂ)} [PreirreducibleSpace B'.left] [Nonempty T.left]
    (b : B' ⟶ B) (I : B.left.IdealSheafData)
    (hblowup : ∀ (A : Over (Spec ↧ℂ)) (f : A ⟶ B),
      (∀ x : A.left, ∃ V : A.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(A.left, V.1)] Γ(A.left, V.1))) →
      ∃! u : A ⟶ B', u ≫ b = f)
    (f : T ⟶ B) [IsDominant f.left] (hf : I.comap f.left = ⊤)
    (g : T ⟶ B') (hg : g ≫ b = f) : IsDominant g.left := by
  let V : B.left.Opens := ⟨(I.support : Set B.left)ᶜ, I.support.isClosed.isOpen_compl⟩
  let U : Over (Spec ↧ℂ) := Over.mk (V.ι ≫ B.hom)
  let ι : U ⟶ B := Over.homMk V.ι rfl
  haveI : IsOpenImmersion ι.left := inferInstanceAs (IsOpenImmersion V.ι)
  have hι : I.comap ι.left = ⊤ :=
    s2v_i2b_comap_eq_top_of_avoids ι.left I (fun x => x.property)
  have hrange : Set.range f.left ⊆ Set.range ι.left := by
    rintro y ⟨x, rfl⟩
    refine ⟨⟨f.left x, ?_⟩, rfl⟩
    change f.left x ∉ I.support
    intro hx
    have hmem : x ∈ (I.comap f.left).support := by
      rw [Scheme.IdealSheafData.support_comap]
      exact hx
    rw [hf, Scheme.IdealSheafData.support_top] at hmem
    exact hmem
  let fU : T ⟶ U := Over.homMk (IsOpenImmersion.lift ι.left f.left hrange) (by
    change IsOpenImmersion.lift ι.left f.left hrange ≫ (ι.left ≫ B.hom) = T.hom
    rw [← Category.assoc, IsOpenImmersion.lift_fac, f.w])
  have hfU : fU ≫ ι = f := by
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac ι.left f.left hrange
  haveI : IsIso (pullback.snd b ι) := s2v_i2b_blowup_isIso_over_unit_ideal b I hblowup ι hι
  let p : T ⟶ pullback b ι := pullback.lift g fU (hg.trans hfU.symm)
  have hp : p ≫ pullback.snd b ι = fU := pullback.lift_snd _ _ _
  haveI : IsDominant (fU.left ≫ ι.left) := by
    change IsDominant (fU ≫ ι).left
    rw [hfU]
    infer_instance
  haveI : IsDominant fU.left := IsDominant.of_comp_of_isOpenImmersion fU.left ι.left
  haveI : IsDominant (p.left ≫ (pullback.snd b ι).left) := by
    change IsDominant (p ≫ pullback.snd b ι).left
    rw [hp]
    infer_instance
  haveI : IsDominant p.left :=
    IsDominant.of_comp_of_isOpenImmersion p.left (pullback.snd b ι).left
  haveI : Nonempty (pullback b ι).left := ⟨p.left (Classical.choice inferInstance)⟩
  haveI : IsOpenImmersion (pullback.fst b ι).left :=
    MorphismProperty.of_isPullback
      (((IsPullback.of_hasPullback b ι).map (Over.forget _)).flip)
      (inferInstance : IsOpenImmersion ι.left)
  haveI : IsDominant (pullback.fst b ι).left :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
      (pullback.fst b ι).left.isOpenEmbedding.isOpenMap⟩
  have hpf : p ≫ pullback.fst b ι = g := pullback.lift_fst _ _ _
  rw [← hpf]
  change IsDominant (p.left ≫ (pullback.fst b ι).left)
  infer_instance

/-- The rank-one criterion on the integral upper stage makes the centre proper on the base.
Source: support of inverse-image ideal sheaves and the retained invertibility criterion. -/
theorem s2v_i2b_center_support_ne_top
    {X Y : Scheme} [IsIntegral X] (f : X ⟶ Y) (I : Y.IdealSheafData)
    (hcartier : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap f).ideal U) ≃ₗ[Γ(X, U.1)] Γ(X, U.1))) :
    I.support ≠ ⊤ := by
  have hp := s2v_cartier_pullback_support_ne_top f I hcartier
  intro hI
  apply hp
  rw [Scheme.IdealSheafData.support_comap, hI]
  rfl

/-- The retained lift of a dominant field source through a blowup is dominant.
Source: the retained blowup universal property and the unit-ideal generic pullback. -/
theorem s2v_i2b_blowup_fieldSource_dominant
    {L : Type} [Field L] {B B' : Over (Spec ↧ℂ)} [IsIntegral B'.left]
    (b : B' ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ x : B'.left, ∃ U : B'.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap b.left).ideal U) ≃ₗ[Γ(B'.left, U.1)] Γ(B'.left, U.1)))
    (hblowup : ∀ (A : Over (Spec ↧ℂ)) (f : A ⟶ B),
      (∀ x : A.left, ∃ V : A.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(A.left, V.1)] Γ(A.left, V.1))) →
      ∃! u : A ⟶ B', u ≫ b = f)
    (η : Spec ↧L ⟶ B.left) [IsDominant η]
    (η' : Spec ↧L ⟶ B'.left) (hη : η' ≫ b.left = η) : IsDominant η' := by
  have hI := s2v_i2b_center_support_ne_top b.left I hcartier
  have hunit := s2v_dominant_fieldSource_comap_eq_top η I hI
  let T : Over (Spec ↧ℂ) := Over.mk (η ≫ B.hom)
  let f : T ⟶ B := Over.homMk η rfl
  let g : T ⟶ B' := Over.homMk η' (by
    change η' ≫ B'.hom = η ≫ B.hom
    rw [← b.w, ← Category.assoc, hη])
  haveI : Nonempty T.left := inferInstanceAs (Nonempty (Spec ↧L))
  haveI : IsDominant f.left := inferInstanceAs (IsDominant η)
  have hg : g ≫ b = f := Over.OverMorphism.ext hη
  exact s2v_i2b_blowup_lift_dominant b I hblowup f hunit g hg

end HodgeLean.Foundations.Program

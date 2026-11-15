import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Lifting paired slices through the retained blowups
Equal restricted branch ideals identify the restricted centre ideal.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Equal restrictions of a pair of branch ideals identify their centre ideal
on the slice. -/
theorem s2e_paired_centre_comap {Q B : Scheme} (ℓ : Q ⟶ B)
    (D₁ D₂ : B.IdealSheafData) (hpair : D₁.comap ℓ = D₂.comap ℓ) :
    (D₁ ⊔ D₂).comap ℓ = D₁.comap ℓ := by
  rw [Scheme.IdealSheafData.comap_sup, ← hpair, sup_idem]

/-- A paired slice with an invertible restricted branch ideal has a unique
lift through the supplied blowup, and that lift remains an immersion. -/
theorem s2e_paired_blowup_slice_lift
    {Q B B' : Over (Spec ↧ℂ)} (b : B' ⟶ B) [IsSeparated b.left]
    (D₁ D₂ : B.left.IdealSheafData)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((D₁ ⊔ D₂).comap f.left).ideal U) ≃ₗ[Γ(T.left, U)]
          Γ(T.left, U))) → ∃! u : T ⟶ B', u ≫ b = f)
    (ℓ : Q ⟶ B) [IsClosedImmersion ℓ.left]
    (hpair : D₁.comap ℓ.left = D₂.comap ℓ.left)
    (hCartier : ∀ x : Q.left, ∃ U : Q.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((D₁.comap ℓ.left).ideal U) ≃ₗ[Γ(Q.left, U)] Γ(Q.left, U))) :
    ∃! u : Q ⟶ B', u ≫ b = ℓ ∧ IsClosedImmersion u.left := by
  have hcentre := s2e_paired_centre_comap ℓ.left D₁ D₂ hpair
  obtain ⟨u, hu, huniq⟩ := hblowup Q ℓ (by rw [hcentre]; exact hCartier)
  have hcomp : IsClosedImmersion (u.left ≫ b.left) := by
    change IsClosedImmersion (u ≫ b).left
    rw [hu]
    infer_instance
  letI := hcomp
  refine ⟨u, ⟨hu, IsClosedImmersion.of_comp u.left b.left⟩, ?_⟩
  intro v hv
  exact huniq v hv.1

/-- The scheme image ideal of a reduced source is the reduced ideal of the
closure of its image. -/
theorem s2e_reduced_image_ideal {Q B : Scheme} [IsReduced Q] (ℓ : Q ⟶ B) :
    ℓ.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range ℓ)) := by
  rw [← Scheme.IdealSheafData.map_bot,
    ← Scheme.nilradical_eq_bot (X := Q),
    ← Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  simp only [TopologicalSpace.Closeds.coe_top, Set.image_univ]

/-- A reduced lifted slice that agrees with the original slice away from the
centre has the prescribed reduced strict-transform ideal. -/
theorem s2e_lifted_slice_strictTransform
    {Q B B' : Scheme} [IsReduced Q] (f : B' ⟶ B)
    (ℓ : Q ⟶ B) (u : Q ⟶ B') [IsClosedImmersion u]
    (K : B.IdealSheafData) (S : Set Q) (hS : Dense S)
    (haway : f ⁻¹' ((ℓ.ker.support : Set B) \ (K.support : Set B)) = u '' S) :
    u.ker = s2c_strictTransform f ℓ.ker K := by
  rw [s2e_reduced_image_ideal u]
  unfold s2c_strictTransform
  congr 1
  apply TopologicalSpace.Closeds.ext
  change closure (Set.range u) = closure (f ⁻¹' _)
  rw [haway, u.isClosedEmbedding.closure_image_eq, hS.closure_eq, Set.image_univ,
    u.isClosedEmbedding.isClosed_range.closure_eq]

/-- The complement of a nonzero ideal on an integral slice is dense. -/
theorem s2e_dense_ideal_complement {Q : Scheme} [IsIntegral Q]
    (I : Q.IdealSheafData) (hI : I ≠ ⊥) : Dense (I.support : Set Q)ᶜ := by
  apply I.support.isClosed.isOpen_compl.dense
  by_contra h
  have htop : I.support = ⊤ := by
    apply TopologicalSpace.Closeds.ext
    ext x
    constructor
    · intro _; trivial
    · intro _
      by_contra hx
      exact h ⟨x, hx⟩
  exact hI (Scheme.IdealSheafData.support_eq_top_iff.mp htop)

/-- An ideal locally isomorphic to the structure sheaf on a nonempty scheme
cannot be the zero ideal. -/
theorem s2e_invertible_ideal_ne_bot {Q : Scheme} [Nonempty Q]
    (I : Q.IdealSheafData)
    (hI : ∀ x : Q, ∃ U : Q.affineOpens, x ∈ U.1 ∧
      Nonempty ((I.ideal U) ≃ₗ[Γ(Q, U)] Γ(Q, U))) : I ≠ ⊥ := by
  intro hzero
  obtain ⟨U, hx, ⟨e⟩⟩ := hI (Classical.ofNonempty : Q)
  letI : Nonempty U.1 := ⟨⟨Classical.ofNonempty, hx⟩⟩
  subst I
  have hbot : (⊥ : Q.IdealSheafData).ideal U = ⊥ := rfl
  rw [hbot] at e
  have hz : e.symm (1 : Γ(Q, U)) = 0 := Subsingleton.elim _ _
  have hone : (1 : Γ(Q, U)) = 0 := by
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg e hz
  exact one_ne_zero hone

/-- The unit ideal meets the local invertibility test in the blowup interface. -/
theorem s2e_unit_ideal_locally_free (Q : Scheme) (x : Q) :
    ∃ U : Q.affineOpens, x ∈ U.1 ∧
      Nonempty ((((⊤ : Q.IdealSheafData).ideal U)) ≃ₗ[Γ(Q, U)] Γ(Q, U)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    Q.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨⟨U, hU⟩, hxU, ?_⟩
  exact ⟨LinearEquiv.ofTop _ rfl⟩

/-- The blowup universal property gives an isomorphism after any base change
on which the centre ideal is the unit ideal. -/
theorem s2e_blowup_isIso_off_centre
    {B B' U : Over (Spec ↧ℂ)} (b : B' ⟶ B) (I : B.left.IdealSheafData)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! u : T ⟶ B', u ≫ b = f)
    (j : U ⟶ B) (hI : I.comap j.left = ⊤) :
    IsIso (pullback.snd b j) := by
  obtain ⟨s, hs, _⟩ := hblowup U j (by
    rw [hI]
    exact s2e_unit_ideal_locally_free U.left)
  have hbase : I.comap ((pullback.fst b j ≫ b).left) = ⊤ := by
    rw [pullback.condition]
    change I.comap ((pullback.snd b j).left ≫ j.left) = ⊤
    rw [Scheme.IdealSheafData.comap_comp, hI, Scheme.IdealSheafData.comap_top]
  obtain ⟨a, _, huniq⟩ := hblowup (pullback b j) (pullback.fst b j ≫ b) (by
    rw [hbase]
    exact s2e_unit_ideal_locally_free (pullback b j).left)
  have hsection : pullback.snd b j ≫ s = pullback.fst b j := by
    apply (huniq _ ?_).trans (huniq _ rfl).symm
    rw [Category.assoc, hs, pullback.condition]
  let t : U ⟶ pullback b j := pullback.lift s (𝟙 U) (by simpa only [Category.id_comp] using hs)
  refine ⟨⟨t, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, t, pullback.lift_fst, Category.id_comp, hsection]
    · simp only [Category.assoc, t, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · exact pullback.lift_snd _ _ _

/-- Avoiding the support of an ideal makes its restriction the unit ideal. -/
theorem s2e_comap_eq_top_of_disjoint
    {Q B : Scheme} (f : Q ⟶ B) (I : B.IdealSheafData)
    (h : Disjoint (Set.range f) (I.support : Set B)) : I.comap f = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff (I.comap f)).mp
  rw [Scheme.IdealSheafData.support_comap]
  apply TopologicalSpace.Closeds.ext
  ext x
  constructor
  · intro hx
    exact (Set.disjoint_left.mp h ⟨x, rfl⟩ hx).elim
  · intro hx
    exact hx.elim

/-- Pointwise injectivity away from the centre identifies the reduced strict
transform of an integral lifted Cartier slice. -/
theorem s2e_cartier_slice_strictTransform
    {Q B B' : Scheme} [IsIntegral Q] (f : B' ⟶ B)
    (ℓ : Q ⟶ B) (u : Q ⟶ B') [IsClosedImmersion ℓ] [IsClosedImmersion u]
    (hfac : u ≫ f = ℓ) (K : B.IdealSheafData)
    (hCartier : ∀ x : Q, ∃ U : Q.affineOpens, x ∈ U.1 ∧
      Nonempty (((K.comap ℓ).ideal U) ≃ₗ[Γ(Q, U)] Γ(Q, U)))
    (hinj : ∀ x y : B', f x ∉ K.support → f x = f y → x = y) :
    u.ker = s2c_strictTransform f ℓ.ker K := by
  have hfu : ∀ q : Q, f (u q) = ℓ q := fun q =>
    congrArg (fun g : Q ⟶ B => g q) hfac
  have hDense := s2e_dense_ideal_complement (K.comap ℓ)
    (s2e_invertible_ideal_ne_bot (K.comap ℓ) hCartier)
  rw [Scheme.IdealSheafData.support_comap] at hDense
  apply s2e_lifted_slice_strictTransform f ℓ u K _ hDense
  rw [Scheme.Hom.support_ker ℓ, ℓ.isClosedEmbedding.isClosed_range.closure_eq]
  ext x
  constructor
  · rintro ⟨⟨q, hq⟩, hx⟩
    refine ⟨q, ?_, ?_⟩
    · change ℓ q ∉ K.support
      rwa [hq]
    · exact hinj (u q) x (by rwa [hfu, hq]) ((hfu q).trans hq)
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨q, (hfu q).symm⟩, ?_⟩
    rw [hfu]
    exact hq

/-- An isomorphic base change over an injective chart makes the original map
injective on the inverse image of that chart. -/
theorem s2e_injective_on_chart_of_pullback_isIso
    {X Y U : Scheme} (f : X ⟶ Y) (j : U ⟶ Y)
    (hj : Function.Injective j) [IsIso (pullback.snd f j)]
    (x y : X) (hx : f x ∈ Set.range j) (hxy : f x = f y) : x = y := by
  have hx' : x ∈ Set.range (pullback.fst f j) := by
    rw [Scheme.Pullback.range_fst]
    exact hx
  have hy' : y ∈ Set.range (pullback.fst f j) := by
    rw [Scheme.Pullback.range_fst]
    change f y ∈ Set.range j
    rwa [← hxy]
  obtain ⟨a, ha⟩ := hx'
  obtain ⟨b, hb⟩ := hy'
  have hpoint (z : ↥(pullback f j : Scheme)) :
      f (pullback.fst f j z) = j (pullback.snd f j z) :=
    congrArg (fun h : (pullback f j : Scheme) ⟶ Y => h z) (pullback.condition (f := f) (g := j))
  have hs : pullback.snd f j a = pullback.snd f j b := by
    apply hj
    rw [← hpoint a, ← hpoint b, ha, hb, hxy]
  have hab := (pullback.snd f j).isOpenEmbedding.injective hs
  exact ha.symm.trans ((congrArg (pullback.fst f j) hab).trans hb)

/-- The retained blowup universal property also controls arbitrary underlying
scheme maps, by equipping their sources with the induced complex structure map. -/
theorem s2e_blowup_universal_property_on_schemes
    {B B' : Over (Spec ↧ℂ)} (b : B' ⟶ B) (I : B.left.IdealSheafData)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! u : T ⟶ B', u ≫ b = f)
    (T : Scheme) (f : T ⟶ B.left)
    (hf : ∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) :
    ∃! u : T ⟶ B'.left, u ≫ b.left = f := by
  let fOver : Over.mk (f ≫ B.hom) ⟶ B := Over.homMk f
  obtain ⟨u, hu, huniq⟩ := hblowup _ fOver hf
  refine ⟨u.left, congrArg Over.Hom.left hu, ?_⟩
  intro v hv
  let vOver : Over.mk (f ≫ B.hom) ⟶ B' := Over.homMk v (by
    rw [← b.w, ← Category.assoc, hv]
    rfl)
  have hvOver : vOver ≫ b = fOver := Over.OverMorphism.ext hv
  exact congrArg Over.Hom.left (huniq vOver hvOver)

/-- The blowup universal property gives an isomorphism after any base change
on which the centre ideal is the unit ideal. -/
theorem s2e_blowup_scheme_isIso_off_centre
    {B B' U : Scheme} (b : B' ⟶ B) (I : B.IdealSheafData)
    (hblowup : ∀ (T : Scheme) (f : T ⟶ B),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ B', u ≫ b = f)
    (j : U ⟶ B) (hI : I.comap j = ⊤) :
    IsIso (pullback.snd b j) := by
  obtain ⟨s, hs, _⟩ := hblowup U j (by
    rw [hI]
    exact s2e_unit_ideal_locally_free U)
  have hbase : I.comap ((pullback.fst b j ≫ b)) = ⊤ := by
    rw [pullback.condition]
    change I.comap ((pullback.snd b j) ≫ j) = ⊤
    rw [Scheme.IdealSheafData.comap_comp, hI, Scheme.IdealSheafData.comap_top]
  obtain ⟨a, _, huniq⟩ := hblowup (pullback b j) (pullback.fst b j ≫ b) (by
    rw [hbase]
    exact s2e_unit_ideal_locally_free (pullback b j))
  have hsection : pullback.snd b j ≫ s = pullback.fst b j := by
    apply (huniq _ ?_).trans (huniq _ rfl).symm
    rw [Category.assoc, hs, pullback.condition]
  let t : U ⟶ pullback b j := pullback.lift s (𝟙 U) (by simpa only [Category.id_comp] using hs)
  refine ⟨⟨t, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, t, pullback.lift_fst, Category.id_comp, hsection]
    · simp only [Category.assoc, t, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · exact pullback.lift_snd _ _ _

/-- A map with the retained blowup property is injective on points away from
its centre. -/
theorem s2e_blowup_injective_off_centre
    {B B' : Scheme} (b : B' ⟶ B) (I : B.IdealSheafData)
    (hblowup : ∀ (T : Scheme) (f : T ⟶ B),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ B', u ≫ b = f)
    (x y : B') (hx : b x ∉ I.support) (hxy : b x = b y) : x = y := by
  let V : B.Opens := ⟨(I.support : Set B)ᶜ, I.support.isClosed.isOpen_compl⟩
  have hI : I.comap V.ι = ⊤ := by
    apply s2e_comap_eq_top_of_disjoint
    rw [Scheme.Opens.range_ι]
    exact Set.disjoint_left.mpr (fun _ hz hi => hz hi)
  letI := s2e_blowup_scheme_isIso_off_centre b I hblowup V.ι hI
  apply s2e_injective_on_chart_of_pullback_isIso b V.ι V.ι.isOpenEmbedding.injective x y ?_ hxy
  rw [Scheme.Opens.range_ι]
  exact hx

/-- A paired integral Cartier slice lifts uniquely through a retained blowup
as an immersion with the actual reduced strict-transform ideal. -/
theorem s2e_paired_blowup_slice_strict_lift
    {Q B B' : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (b : B' ⟶ B) [IsSeparated b.left] (D₁ D₂ : B.left.IdealSheafData)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((D₁ ⊔ D₂).comap f.left).ideal U) ≃ₗ[Γ(T.left, U)]
          Γ(T.left, U))) → ∃! u : T ⟶ B', u ≫ b = f)
    (ℓ : Q ⟶ B) [IsClosedImmersion ℓ.left]
    (hpair : D₁.comap ℓ.left = D₂.comap ℓ.left)
    (hCartier : ∀ x : Q.left, ∃ U : Q.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((D₁.comap ℓ.left).ideal U) ≃ₗ[Γ(Q.left, U)] Γ(Q.left, U))) :
    ∃! u : Q ⟶ B', u ≫ b = ℓ ∧ IsClosedImmersion u.left ∧
      u.left.ker = s2c_strictTransform b.left ℓ.left.ker (D₁ ⊔ D₂) := by
  obtain ⟨u, ⟨hu, himm⟩, huniq⟩ :=
    s2e_paired_blowup_slice_lift b D₁ D₂ hblowup ℓ hpair hCartier
  letI := himm
  have hK : ∀ x : Q.left, ∃ U : Q.left.affineOpens, x ∈ U.1 ∧
      Nonempty ((((D₁ ⊔ D₂).comap ℓ.left).ideal U) ≃ₗ[Γ(Q.left, U)] Γ(Q.left, U)) := by
    rw [s2e_paired_centre_comap ℓ.left D₁ D₂ hpair]
    exact hCartier
  have htrans := s2e_cartier_slice_strictTransform b.left ℓ.left u.left
    (congrArg Over.Hom.left hu) (D₁ ⊔ D₂) hK
    (s2e_blowup_injective_off_centre b.left (D₁ ⊔ D₂)
      (s2e_blowup_universal_property_on_schemes b (D₁ ⊔ D₂) hblowup))
  refine ⟨u, ⟨hu, himm, htrans⟩, ?_⟩
  intro v hv
  exact huniq v ⟨hv.1, hv.2.1⟩

/-- The support of a reduced strict transform lies over the original support. -/
theorem s2e_strictTransform_support_subset
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData) :
    ((s2c_strictTransform f D K).support : Set X) ⊆
      f ⁻¹' (D.support : Set Y) := by
  unfold s2c_strictTransform
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  apply (D.support.isClosed.preimage f.continuous).closure_subset_iff.mpr
  intro x hx
  exact hx.1

/-- Avoidance of a divisor persists along a lifted slice and its reduced
strict transform, without any Cartier requirement on that divisor. -/
theorem s2e_lifted_slice_avoids_strictTransform
    {Q X Y : Scheme} (f : X ⟶ Y) (ℓ : Q ⟶ Y) (u : Q ⟶ X)
    (hfac : u ≫ f = ℓ) (D K : Y.IdealSheafData)
    (havoid : Disjoint (Set.range ℓ) (D.support : Set Y)) :
    Disjoint (Set.range u) ((s2c_strictTransform f D K).support : Set X) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨q, rfl⟩ hx
  have hy := s2e_strictTransform_support_subset f D K hx
  have hpoint : f (u q) = ℓ q := congrArg (fun g : Q ⟶ Y => g q) hfac
  change f (u q) ∈ D.support at hy
  rw [hpoint] at hy
  exact Set.disjoint_left.mp havoid ⟨q, rfl⟩ hy

/-- Once each newly processed pair avoids the slice, all processed branch
transforms avoid the slice at every later tower level. -/
theorem s2e_processed_branches_avoid_tower
    {r : ℕ} {Q : Scheme} (B : Fin (r + 1) → Scheme)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (ℓ : ∀ i, Q ⟶ B i)
    (hfac : ∀ i : Fin r, ℓ i.succ ≫ b i = ℓ i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).IdealSheafData)
    (K : ∀ i : Fin r, (B i.castSucc).IdealSheafData)
    (htransform : ∀ (i : Fin r) t,
      D i.succ t = s2c_strictTransform (b i) (D i.castSucc t) (K i))
    (hnew : ∀ (i : Fin r) (t : Fin (2 * r)),
      2 * i.val ≤ t.val → t.val < 2 * (i.val + 1) →
      Disjoint (Set.range (ℓ i.succ)) ((D i.succ t).support : Set (B i.succ))) :
    ∀ (i : Fin (r + 1)) (t : Fin (2 * r)), t.val < 2 * i.val →
      Disjoint (Set.range (ℓ i)) ((D i t).support : Set (B i)) := by
  intro i
  induction i using Fin.induction with
  | zero =>
      intro t ht
      simp only [Fin.val_zero, mul_zero] at ht
      exact (Nat.not_lt_zero _ ht).elim
  | succ i ih =>
      intro t ht
      by_cases hold : t.val < 2 * i.val
      · rw [htransform]
        exact s2e_lifted_slice_avoids_strictTransform (b i) (ℓ i.castSucc)
          (ℓ i.succ) (hfac i) (D i.castSucc t) (K i) (ih t hold)
      · exact hnew i t (by omega) (by simpa only [Fin.val_succ] using ht)

/-- The support of the reduced strict transform can be computed on any open
scheme chart before taking the topological closure. -/
theorem s2e_strictTransform_support_on_open
    {U X Y : Scheme} (j : U ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ Y) (D K : Y.IdealSheafData) :
    j ⁻¹' ((s2c_strictTransform f D K).support : Set X) =
      closure ((j ≫ f) ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))) := by
  unfold s2c_strictTransform
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  change j ⁻¹' closure (f ⁻¹' _) = _
  rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous]
  rfl

/-- Strict-transform support is the closure of the pulled back branch support
outside the pulled back centre. -/
theorem s2e_strictTransform_support_eq_removed_pullback
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData) :
    ((s2c_strictTransform f D K).support : Set X) =
      closure (((D.comap f).support : Set X) \ ((K.comap f).support : Set X)) := by
  unfold s2c_strictTransform
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
  rfl

end HodgeLean.Foundations.Program








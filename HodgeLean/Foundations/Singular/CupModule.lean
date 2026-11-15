import HodgeLean.Foundations.Singular.SmallCup
import HodgeLean.Foundations.Singular.ConnectingMap
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicTopology.Simplicial
/-!
# Cup multiplication and connecting maps

Degreewise cup multiplication is compatible with the differential by Leibniz.
HC no distance; AV milestone no distance. Stage S4 retires no stated hypothesis.
-/
noncomputable section
namespace HodgeLean.Foundations.Singular
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def shiftScMap (C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ D.X (n + q))
    (hf : ∀ n, f n ≫ D.d (n + q) (n + 1 + q) = C.d n (n + 1) ≫ f (n + 1))
    (n : ℕ) : C.sc n ⟶ D.sc (n + q) := by
  cases n with
  | zero =>
    refine (C.isoSc' 0 0 1 (by simp) (by simp)).hom ≫ ?_ ≫
      (D.isoSc' ((ComplexShape.up ℕ).prev (0 + q)) (0 + q) (1 + q)
        rfl (by simp [CochainComplex.next, Nat.add_comm])).inv
    refine { τ₁ := 0, τ₂ := f 0, τ₃ := f 1, comm₁₂ := ?_, comm₂₃ := hf 0 }
    change (0 : C.X 0 ⟶ D.X ((ComplexShape.up ℕ).prev (0 + q))) ≫ _ = C.d 0 0 ≫ f 0
    rw [zero_comp, C.shape 0 0 (by simp), zero_comp]
  | succ n =>
    refine (C.isoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom ≫ ?_ ≫
      (D.isoSc' (n + q) (n + 1 + q) (n + 2 + q)
        (by rw [show n + 1 + q = (n + q) + 1 by omega]; simp)
        (by simp [CochainComplex.next]; omega)).inv
    exact
      { τ₁ := f n
        τ₂ := f (n + 1)
        τ₃ := f (n + 2)
        comm₁₂ := hf n
        comm₂₃ := hf (n + 1) }

private theorem shiftScMap_τ₂ (C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ D.X (n + q))
    (hf : ∀ n, f n ≫ D.d (n + q) (n + 1 + q) = C.d n (n + 1) ≫ f (n + 1))
    (n : ℕ) : (shiftScMap C D q f hf n).τ₂ = f n := by
  cases n <;> simp [shiftScMap, isoSc', natIsoSc']
private abbrev scComplex (K : SSet.{0}) :=
  (K.chainComplex (ModuleCat.of ℚ ℚ)).linearDualCochainComplex

private def rightCupMap (K : SSet.{0}) (q : ℕ) (β : Cocycle ℚ K q) (n : ℕ) :
    (scComplex K).X n ⟶ (scComplex K).X (n + q) :=
  ModuleCat.ofHom ((HodgeLean.Foundations.Simplicial.cupCochain K n q).flip β.1)

private theorem dual_cast (K : SSet.{0}) {i j : ℕ} (h : i = j)
    (φ : Cochain ℚ K i) :
    ((scComplex K).XIsoOfEq h).hom.hom φ =
      φ.comp ((K.chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq h.symm).hom.hom := by
  subst j
  rfl

private theorem rightCupMap_comm (K : SSet.{0}) (q : ℕ) (β : Cocycle ℚ K q) (n : ℕ) :
    rightCupMap K q β n ≫ (scComplex K).d (n + q) (n + 1 + q) =
      (scComplex K).d n (n + 1) ≫ rightCupMap K q β (n + 1) := by
  apply (cancel_mono ((scComplex K).XIsoOfEq (show n + 1 + q = n + q + 1 by omega)).hom).mp
  rw [Category.assoc, d_comp_XIsoOfEq_hom]
  ext φ
  change coboundary ℚ (n + q) (HodgeLean.Foundations.Simplicial.cupCochain K n q φ β.1) =
    ((scComplex K).XIsoOfEq (show n + 1 + q = n + q + 1 by omega)).hom.hom
      (HodgeLean.Foundations.Simplicial.cupCochain K (n + 1) q (coboundary ℚ n φ) β.1)
  rw [dual_cast, HodgeLean.Foundations.Simplicial.coboundary_cupCochain,
    show coboundary ℚ q β.1 = 0 from β.2, map_zero, smul_zero, add_zero]
  rfl

private def biprodShift (C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ C.X (n + q)) (g : ∀ n, D.X n ⟶ D.X (n + q)) (n : ℕ) :
    (C ⊞ D).X n ⟶ (C ⊞ D).X (n + q) :=
  (biprod.fst : C ⊞ D ⟶ C).f n ≫ f n ≫ (biprod.inl : C ⟶ C ⊞ D).f (n + q) +
  (biprod.snd : C ⊞ D ⟶ D).f n ≫ g n ≫ (biprod.inr : D ⟶ C ⊞ D).f (n + q)

private theorem biprodShift_fst (C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ C.X (n + q)) (g : ∀ n, D.X n ⟶ D.X (n + q)) (n : ℕ) :
    biprodShift C D q f g n ≫ (biprod.fst : C ⊞ D ⟶ C).f (n + q) =
      (biprod.fst : C ⊞ D ⟶ C).f n ≫ f n := by
  simp only [biprodShift, Preadditive.add_comp, Category.assoc,
    biprod_inl_fst_f, biprod_inr_fst_f, Category.comp_id, comp_zero, add_zero]

private theorem biprodShift_snd (C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ C.X (n + q)) (g : ∀ n, D.X n ⟶ D.X (n + q)) (n : ℕ) :
    biprodShift C D q f g n ≫ (biprod.snd : C ⊞ D ⟶ D).f (n + q) =
      (biprod.snd : C ⊞ D ⟶ D).f n ≫ g n := by
  simp only [biprodShift, Preadditive.add_comp, Category.assoc,
    biprod_inl_snd_f, biprod_inr_snd_f, Category.comp_id, comp_zero, zero_add]

private theorem biprodShift_comm (C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ C.X (n + q)) (g : ∀ n, D.X n ⟶ D.X (n + q))
    (hf : ∀ n, f n ≫ C.d (n + q) (n + 1 + q) = C.d n (n + 1) ≫ f (n + 1))
    (hg : ∀ n, g n ≫ D.d (n + q) (n + 1 + q) = D.d n (n + 1) ≫ g (n + 1))
    (n : ℕ) :
    biprodShift C D q f g n ≫ (C ⊞ D).d (n + q) (n + 1 + q) =
      (C ⊞ D).d n (n + 1) ≫ biprodShift C D q f g (n + 1) := by
  apply biprodX_ext_to
  · rw [Category.assoc, ← (biprod.fst : C ⊞ D ⟶ C).comm,
      ← Category.assoc, biprodShift_fst, Category.assoc, hf,
      ← Category.assoc, (biprod.fst : C ⊞ D ⟶ C).comm,
      Category.assoc, Category.assoc, biprodShift_fst]
  · rw [Category.assoc, ← (biprod.snd : C ⊞ D ⟶ D).comm,
      ← Category.assoc, biprodShift_snd, Category.assoc, hg,
      ← Category.assoc, (biprod.snd : C ⊞ D ⟶ D).comm,
      Category.assoc, Category.assoc, biprodShift_snd]

private def pullCocycle {K L : SSet.{0}} (f : K ⟶ L) (q : ℕ) (β : Cocycle ℚ L q) :
    Cocycle ℚ K q :=
  ⟨cochainMap ℚ f q β.1, by
    change coboundary ℚ q (cochainMap ℚ f q β.1) = 0
    rw [HodgeLean.Foundations.Simplicial.coboundary_cochainMap, β.2, map_zero]⟩

private abbrev cochainHom {K L : SSet.{0}} (f : K ⟶ L) :=
  linearDualMap (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ))

private theorem rightCupMap_naturality {K L : SSet.{0}} (f : K ⟶ L) (q : ℕ)
    (β : Cocycle ℚ L q) (n : ℕ) :
    (cochainHom f).f n ≫ rightCupMap K q (pullCocycle f q β) n =
      rightCupMap L q β n ≫ (cochainHom f).f (n + q) := by
  ext φ
  exact (HodgeLean.Foundations.Simplicial.cupCochain_naturality L f n q φ β.1).symm

private theorem cochainHom_comp {K L M : SSet.{0}} (f : K ⟶ L) (g : L ⟶ M) :
    cochainHom (f ≫ g) = cochainHom g ≫ cochainHom f := by
  unfold cochainHom
  let F := (SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  change linearDualMap (F.map (f ≫ g)) = linearDualMap (F.map g) ≫ linearDualMap (F.map f)
  rw [F.map_comp]
  exact linearDualMap_comp _ _

private theorem pullCocycle_comp {K L M : SSet.{0}} (f : K ⟶ L) (g : L ⟶ M)
    (q : ℕ) (β : Cocycle ℚ M q) :
    pullCocycle f q (pullCocycle g q β) = pullCocycle (f ≫ g) q β := by
  apply Subtype.ext
  exact (ConcreteCategory.congr_hom
    (congrArg (fun t : scComplex M ⟶ scComplex K => t.f q) (cochainHom_comp f g)) β.1).symm

private theorem biprodShift_lift (W C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ C.X (n + q)) (g : ∀ n, D.X n ⟶ D.X (n + q))
    (h : ∀ n, W.X n ⟶ W.X (n + q)) (u : W ⟶ C) (v : W ⟶ D)
    (hu : ∀ n, u.f n ≫ f n = h n ≫ u.f (n + q))
    (hv : ∀ n, v.f n ≫ g n = h n ≫ v.f (n + q)) (n : ℕ) :
    (biprod.lift u v).f n ≫ biprodShift C D q f g n =
      h n ≫ (biprod.lift u v).f (n + q) := by
  apply biprodX_ext_to
  · rw [Category.assoc, biprodShift_fst, ← Category.assoc, ← comp_f, biprod.lift_fst,
      hu, Category.assoc, ← comp_f, biprod.lift_fst]
  · rw [Category.assoc, biprodShift_snd, ← Category.assoc, ← comp_f, biprod.lift_snd,
      hv, Category.assoc, ← comp_f, biprod.lift_snd]

private theorem inl_biprodShift (C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ C.X (n + q)) (g : ∀ n, D.X n ⟶ D.X (n + q)) (n : ℕ) :
    (biprod.inl : C ⟶ C ⊞ D).f n ≫ biprodShift C D q f g n =
      f n ≫ (biprod.inl : C ⟶ C ⊞ D).f (n + q) := by
  simp only [biprodShift, Preadditive.comp_add, ← Category.assoc,
    biprod_inl_fst_f, biprod_inl_snd_f, Category.id_comp, zero_comp, add_zero]

private theorem inr_biprodShift (C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ C.X (n + q)) (g : ∀ n, D.X n ⟶ D.X (n + q)) (n : ℕ) :
    (biprod.inr : D ⟶ C ⊞ D).f n ≫ biprodShift C D q f g n =
      g n ≫ (biprod.inr : D ⟶ C ⊞ D).f (n + q) := by
  simp only [biprodShift, Preadditive.comp_add, ← Category.assoc,
    biprod_inr_fst_f, biprod_inr_snd_f, Category.id_comp, zero_comp, zero_add]

private theorem biprodShift_desc (W C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ C.X (n + q)) (g : ∀ n, D.X n ⟶ D.X (n + q))
    (h : ∀ n, W.X n ⟶ W.X (n + q)) (u : C ⟶ W) (v : D ⟶ W)
    (hu : ∀ n, f n ≫ u.f (n + q) = u.f n ≫ h n)
    (hv : ∀ n, g n ≫ v.f (n + q) = v.f n ≫ h n) (n : ℕ) :
    biprodShift C D q f g n ≫ (biprod.desc u v).f (n + q) =
      (biprod.desc u v).f n ≫ h n := by
  apply biprodX_ext_from
  · rw [← Category.assoc, inl_biprodShift, Category.assoc, ← comp_f, biprod.inl_desc,
      hu, ← Category.assoc, ← comp_f, biprod.inl_desc]
  · rw [← Category.assoc, inr_biprodShift, Category.assoc, ← comp_f, biprod.inr_desc,
      hv, ← Category.assoc, ← comp_f, biprod.inr_desc]

private def conjugateShift (C D : CochainComplex (ModuleCat ℚ) ℕ) (e : C ≅ D)
    (q : ℕ) (f : ∀ n, D.X n ⟶ D.X (n + q)) (n : ℕ) : C.X n ⟶ C.X (n + q) :=
  e.hom.f n ≫ f n ≫ e.inv.f (n + q)

private theorem conjugateShift_comm (C D : CochainComplex (ModuleCat ℚ) ℕ) (e : C ≅ D)
    (q : ℕ) (f : ∀ n, D.X n ⟶ D.X (n + q))
    (hf : ∀ n, f n ≫ D.d (n + q) (n + 1 + q) = D.d n (n + 1) ≫ f (n + 1))
    (n : ℕ) :
    conjugateShift C D e q f n ≫ C.d (n + q) (n + 1 + q) =
      C.d n (n + 1) ≫ conjugateShift C D e q f (n + 1) := by
  simp only [conjugateShift, Category.assoc]
  rw [e.inv.comm, ← Category.assoc (f n), hf,
    Category.assoc, ← Category.assoc (e.hom.f n), e.hom.comm]
  simp only [Category.assoc]

open AlgebraicTopology.Singular

private abbrev mvBiprodIso (Y : TopCat.{0}) (A B : Set Y) :=
  dualBiprodIso (SingularChainComplex ℚ (TopCat.of A)) (SingularChainComplex ℚ (TopCat.of B))

private theorem mv_f_pair (Y : TopCat.{0}) (A B : Set Y) :
    (mvCochainShortComplex Y A B).f ≫ (mvBiprodIso Y A B).hom =
      biprod.lift (cochainHom (subsetLeftToSmallSingularSet Y A B))
        (cochainHom (subsetRightToSmallSingularSet Y A B)) := by
  dsimp only [mvCochainShortComplex, dualCochainShortComplex]
  apply biprod.hom_ext
  · simp only [Category.assoc, mvBiprodIso, dualBiprodIso, biprod.lift_fst]
    rw [← linearDualMap_comp]
    change linearDualMap ((biprod.inl : SingularChainComplex ℚ (TopCat.of A) ⟶ _) ≫
      biprod.desc _ _) = _
    rw [biprod.inl_desc]
    exact (biprod.lift_fst _ _).symm
  · simp only [Category.assoc, mvBiprodIso, dualBiprodIso, biprod.lift_snd]
    rw [← linearDualMap_comp]
    change linearDualMap ((biprod.inr : SingularChainComplex ℚ (TopCat.of B) ⟶ _) ≫
      biprod.desc _ _) = _
    rw [biprod.inr_desc]
    exact (biprod.lift_snd _ _).symm

private theorem dual_neg {C D : ChainComplex (ModuleCat ℚ) ℕ} (f : C ⟶ D) :
    linearDualMap (-f) = -linearDualMap f := by
  ext n φ
  apply LinearMap.ext
  intro x
  change Module.Dual ℚ (D.X n) at φ
  change φ (-(f.f n).hom x) = -(φ ((f.f n).hom x))
  exact map_neg φ _

private theorem mv_g_pair (Y : TopCat.{0}) (A B : Set Y) :
    (mvBiprodIso Y A B).inv ≫ (mvCochainShortComplex Y A B).g =
      biprod.desc (cochainHom (TopCat.toSSet.map (subsetIntersectionToLeft Y A B)))
        (-cochainHom (TopCat.toSSet.map (subsetIntersectionToRight Y A B))) := by
  dsimp only [mvCochainShortComplex, dualCochainShortComplex]
  apply biprod.hom_ext'
  · simp only [mvBiprodIso, dualBiprodIso, biprod.inl_desc_assoc, biprod.inl_desc]
    rw [← linearDualMap_comp]
    change linearDualMap (biprod.lift _ _ ≫ biprod.fst) = _
    rw [biprod.lift_fst]
  · simp only [mvBiprodIso, dualBiprodIso, biprod.inr_desc_assoc, biprod.inr_desc]
    rw [← linearDualMap_comp]
    change linearDualMap (biprod.lift _ _ ≫ biprod.snd) = _
    rw [biprod.lift_snd, dual_neg]

private structure CupOperation where
  map (K : SSet.{0}) (q : ℕ) (β : Cocycle ℚ K q) (n : ℕ) :
    (scComplex K).X n ⟶ (scComplex K).X (n + q)
  comm (K : SSet.{0}) (q : ℕ) (β : Cocycle ℚ K q) (n : ℕ) :
    map K q β n ≫ (scComplex K).d (n + q) (n + 1 + q) =
      (scComplex K).d n (n + 1) ≫ map K q β (n + 1)
  natural {K L : SSet.{0}} (f : K ⟶ L) (q : ℕ) (β : Cocycle ℚ L q) (n : ℕ) :
    (cochainHom f).f n ≫ map K q (pullCocycle f q β) n =
      map L q β n ≫ (cochainHom f).f (n + q)

private def rightOperation : CupOperation :=
  ⟨rightCupMap, rightCupMap_comm, rightCupMap_naturality⟩

private def leftRawMap (K : SSet.{0}) (q : ℕ) (β : Cocycle ℚ K q) (n : ℕ) :
    (scComplex K).X n ⟶ (scComplex K).X (q + n) :=
  ModuleCat.ofHom (HodgeLean.Foundations.Simplicial.cupCochain K q n β.1)

private theorem leftRawMap_comm (K : SSet.{0}) (q : ℕ) (β : Cocycle ℚ K q) (n : ℕ) :
    leftRawMap K q β n ≫ (scComplex K).d (q + n) (q + (n + 1)) =
      (-1 : ℚ) ^ q • ((scComplex K).d n (n + 1) ≫ leftRawMap K q β (n + 1)) := by
  ext φ
  change coboundary ℚ (q + n) (HodgeLean.Foundations.Simplicial.cupCochain K q n β.1 φ) =
    (-1 : ℚ) ^ q • HodgeLean.Foundations.Simplicial.cupCochain K q (n + 1) β.1 (coboundary ℚ n φ)
  rw [HodgeLean.Foundations.Simplicial.coboundary_cupCochain,
    show coboundary ℚ q β.1 = 0 from β.2, map_zero]
  simp only [LinearMap.zero_apply, LinearMap.zero_comp, zero_add]

private def leftCupMap (K : SSet.{0}) (q : ℕ) (β : Cocycle ℚ K q) (n : ℕ) :
    (scComplex K).X n ⟶ (scComplex K).X (n + q) :=
  (-1 : ℚ) ^ (q * n) •
    (leftRawMap K q β n ≫ ((scComplex K).XIsoOfEq (Nat.add_comm q n)).hom)

private theorem leftCupMap_comm (K : SSet.{0}) (q : ℕ) (β : Cocycle ℚ K q) (n : ℕ) :
    leftCupMap K q β n ≫ (scComplex K).d (n + q) (n + 1 + q) =
      (scComplex K).d n (n + 1) ≫ leftCupMap K q β (n + 1) := by
  apply (cancel_mono ((scComplex K).XIsoOfEq (Nat.add_comm (n + 1) q)).hom).mp
  simp only [leftCupMap, Linear.smul_comp, Linear.comp_smul,
    Category.assoc, XIsoOfEq_hom_comp_d, d_comp_XIsoOfEq_hom,
    XIsoOfEq_hom_comp_XIsoOfEq_hom, XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  rw [leftRawMap_comm, smul_smul]
  congr 1
  rw [Nat.mul_add, Nat.mul_one, pow_add]

private theorem leftCupMap_naturality {K L : SSet.{0}} (f : K ⟶ L) (q : ℕ)
    (β : Cocycle ℚ L q) (n : ℕ) :
    (cochainHom f).f n ≫ leftCupMap K q (pullCocycle f q β) n =
      leftCupMap L q β n ≫ (cochainHom f).f (n + q) := by
  have hr : (cochainHom f).f n ≫ leftRawMap K q (pullCocycle f q β) n =
      leftRawMap L q β n ≫ (cochainHom f).f (q + n) := by
    ext φ
    exact (HodgeLean.Foundations.Simplicial.cupCochain_naturality L f q n β.1 φ).symm
  simp only [leftCupMap, Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [← Category.assoc, hr, Category.assoc, XIsoOfEq_hom_naturality]

private def leftOperation : CupOperation :=
  ⟨leftCupMap, leftCupMap_comm, leftCupMap_naturality⟩

section Operation
variable (μ : CupOperation)

private def mvRightMiddle (Y : TopCat.{0}) (A B : Set Y) (q : ℕ)
    (β : Cocycle ℚ (TwoSubsetSmallSingularSet Y A B) q) (n : ℕ) :
    (mvCochainShortComplex Y A B).X₂.X n ⟶
      (mvCochainShortComplex Y A B).X₂.X (n + q) :=
  conjugateShift _ _ (mvBiprodIso Y A B) q
    (biprodShift _ _ q
      (μ.map _ q (pullCocycle (subsetLeftToSmallSingularSet Y A B) q β))
      (μ.map _ q (pullCocycle (subsetRightToSmallSingularSet Y A B) q β))) n

private theorem mvRightMiddle_comm (Y : TopCat.{0}) (A B : Set Y) (q : ℕ)
    (β : Cocycle ℚ (TwoSubsetSmallSingularSet Y A B) q) (n : ℕ) :
    mvRightMiddle μ Y A B q β n ≫ (mvCochainShortComplex Y A B).X₂.d (n + q) (n + 1 + q) =
      (mvCochainShortComplex Y A B).X₂.d n (n + 1) ≫ mvRightMiddle μ Y A B q β (n + 1) :=
  conjugateShift_comm _ _ _ q _
    (biprodShift_comm _ _ q _ _ (μ.comm _ _ _) (μ.comm _ _ _)) n

private theorem mvRightMiddle_f (Y : TopCat.{0}) (A B : Set Y) (q : ℕ)
    (β : Cocycle ℚ (TwoSubsetSmallSingularSet Y A B) q) (n : ℕ) :
    (mvCochainShortComplex Y A B).f.f n ≫ mvRightMiddle μ Y A B q β n =
      μ.map _ q β n ≫ (mvCochainShortComplex Y A B).f.f (n + q) := by
  let e := mvBiprodIso Y A B
  apply (cancel_mono (e.hom.f (n + q))).mp
  simp only [mvRightMiddle, conjugateShift, Category.assoc]
  rw [← comp_f, e.inv_hom_id, id_f, Category.comp_id,
    ← Category.assoc, ← comp_f, mv_f_pair, ← comp_f, mv_f_pair]
  exact biprodShift_lift _ _ _ q _ _ _ _ _
    (μ.natural _ _ _) (μ.natural _ _ _) n

private def overlapCocycle (Y : TopCat.{0}) (A B : Set Y) (q : ℕ)
    (β : Cocycle ℚ (TwoSubsetSmallSingularSet Y A B) q) :=
  pullCocycle (TopCat.toSSet.map (subsetIntersectionToLeft Y A B) ≫
    subsetLeftToSmallSingularSet Y A B) q β

private theorem mvRightMiddle_g (Y : TopCat.{0}) (A B : Set Y) (q : ℕ)
    (β : Cocycle ℚ (TwoSubsetSmallSingularSet Y A B) q) (n : ℕ) :
    mvRightMiddle μ Y A B q β n ≫ (mvCochainShortComplex Y A B).g.f (n + q) =
      (mvCochainShortComplex Y A B).g.f n ≫ μ.map _ q (overlapCocycle Y A B q β) n := by
  let e := mvBiprodIso Y A B
  have hl := μ.natural (TopCat.toSSet.map (subsetIntersectionToLeft Y A B)) q
    (pullCocycle (subsetLeftToSmallSingularSet Y A B) q β) n
  rw [pullCocycle_comp] at hl
  have hr := μ.natural (TopCat.toSSet.map (subsetIntersectionToRight Y A B)) q
    (pullCocycle (subsetRightToSmallSingularSet Y A B) q β) n
  rw [pullCocycle_comp, ← (subsetSmallSingularSquare_isPushout Y A B).w] at hr
  apply (cancel_epi (e.inv.f n)).mp
  simp only [mvRightMiddle, conjugateShift, Category.assoc]
  rw [← Category.assoc (e.inv.f n), ← comp_f, e.inv_hom_id, id_f, Category.id_comp,
    ← comp_f, mv_g_pair, ← Category.assoc, ← comp_f, mv_g_pair]
  apply biprodShift_desc
  · intro n
    simpa only [pullCocycle_comp, overlapCocycle] using (μ.natural
      (TopCat.toSSet.map (subsetIntersectionToLeft Y A B)) q
      (pullCocycle (subsetLeftToSmallSingularSet Y A B) q β) n).symm
  · intro n
    change _ ≫ (-((cochainHom (TopCat.toSSet.map (subsetIntersectionToRight Y A B))).f (n + q))) =
      (-((cochainHom (TopCat.toSSet.map (subsetIntersectionToRight Y A B))).f n)) ≫ _
    rw [Preadditive.comp_neg, Preadditive.neg_comp]
    apply congrArg Neg.neg
    have h := μ.natural (TopCat.toSSet.map (subsetIntersectionToRight Y A B)) q
      (pullCocycle (subsetRightToSmallSingularSet Y A B) q β) n
    rw [pullCocycle_comp, ← (subsetSmallSingularSquare_isPushout Y A B).w] at h
    exact h.symm

private def shiftScMapTo (C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ D.X (n + q))
    (hf : ∀ n, f n ≫ D.d (n + q) (n + 1 + q) = C.d n (n + 1) ≫ f (n + 1))
    (n k : ℕ) (h : n + q = k) : C.sc n ⟶ D.sc k := by
  subst k
  exact shiftScMap C D q f hf n

private theorem shiftScMapTo_τ₂ (C D : CochainComplex (ModuleCat ℚ) ℕ) (q : ℕ)
    (f : ∀ n, C.X n ⟶ D.X (n + q))
    (hf : ∀ n, f n ≫ D.d (n + q) (n + 1 + q) = C.d n (n + 1) ≫ f (n + 1))
    (n k : ℕ) (h : n + q = k) :
    (shiftScMapTo C D q f hf n k h).τ₂ = f n ≫ (D.XIsoOfEq h).hom := by
  subst k
  simpa only [shiftScMapTo, XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id] using shiftScMap_τ₂ C D q f hf n

private def rightCupHomology (K : SSet.{0}) (q : ℕ) (β : Cocycle ℚ K q)
    (n k : ℕ) (h : n + q = k) : (scComplex K).homology n ⟶ (scComplex K).homology k :=
  ShortComplex.homologyMap
    (shiftScMapTo _ _ q (μ.map K q β) (μ.comm K q β) n k h)

private theorem small_connecting_cup (Y : TopCat.{0}) (A B : Set Y) (q : ℕ)
    (β : Cocycle ℚ (TwoSubsetSmallSingularSet Y A B) q) (n : ℕ) :
    rightCupHomology μ _ q (overlapCocycle Y A B q β) n (n + q) rfl ≫
      (mvCochainShortComplex_shortExact Y A B).δ (n + q) (n + q + 1) (by simp) =
    (mvCochainShortComplex_shortExact Y A B).δ n (n + 1) (by simp) ≫
      rightCupHomology μ _ q β (n + 1) (n + q + 1) (by omega) := by
  let S := mvCochainShortComplex Y A B
  let h : n + 1 + q = n + q + 1 := by omega
  apply connectingMap_degreewise S S (mvCochainShortComplex_shortExact Y A B)
    (mvCochainShortComplex_shortExact Y A B) n (n + q)
    (shiftScMapTo _ _ q (μ.map _ q (overlapCocycle Y A B q β))
      (μ.comm _ q _) n (n + q) rfl)
    (mvRightMiddle μ Y A B q β n)
    (mvRightMiddle μ Y A B q β (n + 1) ≫ (S.X₂.XIsoOfEq h).hom)
    (shiftScMapTo _ _ q (μ.map _ q β) (μ.comm _ q β)
      (n + 1) (n + q + 1) h)
  · rw [shiftScMapTo_τ₂]
    simp only [XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
    exact mvRightMiddle_g μ Y A B q β n
  · rw [shiftScMapTo_τ₂, Category.assoc, ← XIsoOfEq_hom_naturality,
      ← Category.assoc]
    exact congrArg (fun t => t ≫ (S.X₂.XIsoOfEq h).hom) (mvRightMiddle_f μ Y A B q β (n + 1)).symm
  · rw [← Category.assoc, ← mvRightMiddle_comm μ, Category.assoc, d_comp_XIsoOfEq_hom]

private theorem homologyMap_ext_middle {S T : ShortComplex (ModuleCat ℚ)}
    (f g : S ⟶ T) (h : f.τ₂ = g.τ₂) :
    ShortComplex.homologyMap f = ShortComplex.homologyMap g := by
  apply (cancel_epi S.homologyπ).mp
  rw [ShortComplex.homologyπ_naturality, ShortComplex.homologyπ_naturality]
  congr 1
  apply (cancel_mono T.iCycles).mp
  rw [ShortComplex.cyclesMap_i, ShortComplex.cyclesMap_i, h]

private theorem rightCupHomology_naturality {K L : SSet.{0}} (f : K ⟶ L) (q : ℕ)
    (β : Cocycle ℚ L q) (n k : ℕ) (h : n + q = k) :
    homologyMap (cochainHom f) n ≫ rightCupHomology μ K q (pullCocycle f q β) n k h =
      rightCupHomology μ L q β n k h ≫ homologyMap (cochainHom f) k := by
  change ShortComplex.homologyMap ((shortComplexFunctor _ _ n).map (cochainHom f)) ≫
    ShortComplex.homologyMap _ = ShortComplex.homologyMap _ ≫
      ShortComplex.homologyMap ((shortComplexFunctor _ _ k).map (cochainHom f))
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  apply homologyMap_ext_middle
  change (cochainHom f).f n ≫
    (shiftScMapTo (scComplex K) (scComplex K) q (μ.map K q (pullCocycle f q β))
      (μ.comm K q (pullCocycle f q β)) n k h).τ₂ =
    (shiftScMapTo (scComplex L) (scComplex L) q (μ.map L q β)
      (μ.comm L q β) n k h).τ₂ ≫ (cochainHom f).f k
  rw [shiftScMapTo_τ₂, shiftScMapTo_τ₂, ← Category.assoc,
    μ.natural, Category.assoc, XIsoOfEq_hom_naturality, ← Category.assoc]

end Operation

private theorem rightCupHomology_eq (Y : TopCat.{0}) (q : ℕ)
    (β : Cocycle ℚ (TopCat.toSSet.obj Y) q) (n k : ℕ) (h : n + q = k) :
    rightCupHomology rightOperation (TopCat.toSSet.obj Y) q β n k h =
      ModuleCat.ofHom ((cup Y h).flip (cohomologyClass Y q β)) := by
  apply ModuleCat.hom_ext
  apply homologyMap_cup_right Y n q k h β
  intro φ
  rw [shiftScMapTo_τ₂]
  exact dual_cast (TopCat.toSSet.obj Y) h (cupCochain Y n q φ β.1)

private theorem leftCupHomology_eq (Y : TopCat.{0}) (q : ℕ)
    (β : Cocycle ℚ (TopCat.toSSet.obj Y) q) (n k : ℕ) (h : n + q = k) :
    rightCupHomology leftOperation (TopCat.toSSet.obj Y) q β n k h =
      ModuleCat.ofHom ((-1 : ℚ) ^ (q * n) •
        cup Y (show q + n = k by omega) (cohomologyClass Y q β)) := by
  apply ModuleCat.hom_ext
  apply homologyMap_cup_left Y n q k (by omega) β ((-1 : ℚ) ^ (q * n))
  intro φ
  rw [shiftScMapTo_τ₂]
  change ((scComplex (TopCat.toSSet.obj Y)).XIsoOfEq h).hom.hom
    ((-1 : ℚ) ^ (q * n) •
      ((scComplex (TopCat.toSSet.obj Y)).XIsoOfEq (Nat.add_comm q n)).hom.hom
        (cupCochain Y q n β.1 φ)) = _
  rw [map_smul]
  congr 1
  change (((scComplex (TopCat.toSSet.obj Y)).XIsoOfEq (Nat.add_comm q n)).hom ≫
    ((scComplex (TopCat.toSSet.obj Y)).XIsoOfEq h).hom).hom (cupCochain Y q n β.1 φ) = _
  rw [XIsoOfEq_hom_comp_XIsoOfEq_hom]
  exact dual_cast (TopCat.toSSet.obj Y) _ (cupCochain Y q n β.1 φ)

private theorem mvδ_operation (μ : CupOperation) (Y : TopCat.{0}) (A B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ) (p q k : ℕ) (hk : p + q = k)
    (β : Cocycle ℚ (TopCat.toSSet.obj Y) q) :
    rightCupHomology μ (TopCat.toSSet.obj (TopCat.of ↥(A ∩ B))) q
      (pullCocycle (TopCat.toSSet.map (topologicalSubsetInclusion Y (A ∩ B))) q β)
      p k hk ≫ ModuleCat.ofHom (mvδ Y A B hA hB hc k) =
    ModuleCat.ofHom (mvδ Y A B hA hB hc p) ≫
      rightCupHomology μ (TopCat.toSSet.obj Y) q β (p + 1) (k + 1) (by omega) := by
  subst k
  let S := mvCochainShortComplex Y A B
  let i := (subsetSingularSubcomplex Y A ⊔ subsetSingularSubcomplex Y B).ι
  let βs := pullCocycle i q β
  let e (n : ℕ) := (smallCochainCohomologyEquiv Y A B hA hB hc n).toModuleIso
  have hi : overlapCocycle Y A B q βs =
      pullCocycle (TopCat.toSSet.map (topologicalSubsetInclusion Y (A ∩ B))) q β := by
    unfold overlapCocycle βs
    rw [pullCocycle_comp]
    congr 1
  have hn := rightCupHomology_naturality μ i q β (p + 1) (p + q + 1) (by omega)
  change (e (p + 1)).inv ≫ rightCupHomology μ _ q βs (p + 1) (p + q + 1) _ =
    rightCupHomology μ _ q β (p + 1) (p + q + 1) _ ≫ (e (p + q + 1)).inv at hn
  have ht : rightCupHomology μ _ q βs (p + 1) (p + q + 1) (by omega) ≫ (e (p + q + 1)).hom =
      (e (p + 1)).hom ≫ rightCupHomology μ _ q β (p + 1) (p + q + 1) (by omega) := by
    apply (cancel_epi (e (p + 1)).inv).mp
    rw [← Category.assoc, hn, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hm := congrArg (fun f => f ≫ (e (p + q + 1)).hom)
    (small_connecting_cup μ Y A B q βs p)
  simp only [Category.assoc] at hm
  rw [ht, hi] at hm
  exact hm


/-- Mayer–Vietoris is a right module map for cup multiplication by a global cocycle.
The chain sequence uses `(i, -j)` and addition; its dual cochain sequence uses
restriction and first restriction minus second restriction. With this convention
there is no sign in right multiplication. The proof uses degreewise cocycle lifts
through `δ_eq`, not naturality for a degree-preserving map of complexes.
Source: Hatcher, *Algebraic Topology*, §3.1 (connecting homomorphism) and §3.2,
Lemma 3.6 (Leibniz rule); the degreewise comparison is constructed here.
HC no distance; AV milestone no distance. Stage S4 retires no stated hypothesis.
-/
theorem mvδ_cup_right (Y : TopCat.{0}) (A B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ) (p q : ℕ)
    (β : Cocycle ℚ (TopCat.toSSet.obj Y) q)
    (α : Cohomology ℚ (TopCat.of ↥(A ∩ B)) p) :
    mvδ Y A B hA hB hc (p + q)
      (cup (TopCat.of ↥(A ∩ B)) rfl α
        (cohomologyMap ℚ q (topologicalSubsetInclusion Y (A ∩ B)) (cohomologyClass Y q β))) =
    cup Y (show (p + 1) + q = (p + q) + 1 by omega)
      (mvδ Y A B hA hB hc p α) (cohomologyClass Y q β) := by
  have hm := mvδ_operation rightOperation Y A B hA hB hc p q (p + q) rfl β
  rw [rightCupHomology_eq, rightCupHomology_eq] at hm
  have hclass := cohomologyMap_class Y (topologicalSubsetInclusion Y (A ∩ B)) q β
    (pullCocycle (TopCat.toSSet.map (topologicalSubsetInclusion Y (A ∩ B))) q β) rfl
  rw [← hclass] at hm
  exact ConcreteCategory.congr_hom hm α

example (Y : TopCat.{0}) (A B : Set Y) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q : ℕ) (β : Cocycle ℚ (TopCat.toSSet.obj Y) q) :
    mvδ Y A B hA hB hc (p + q)
      (cup (TopCat.of ↥(A ∩ B)) rfl 0
        (cohomologyMap ℚ q (topologicalSubsetInclusion Y (A ∩ B)) (cohomologyClass Y q β))) =
      cup Y (show (p + 1) + q = (p + q) + 1 by omega)
        (mvδ Y A B hA hB hc p 0) (cohomologyClass Y q β) :=
  mvδ_cup_right Y A B hA hB hc p q β 0

/-- Left multiplication by a global degree-`q` cocycle gives the sign `(-1)^q`
when a degree-zero overlap class crosses the Mayer–Vietoris connecting map.
Source: Hatcher, *Algebraic Topology*, §3.2, Lemma 3.6, and the explicit connecting
construction of §3.1. The convention is the same first-minus-second map as `mvδ_cup_right`.
-/
theorem mvδ_cup_left_zero (Y : TopCat.{0}) (A B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ) (q : ℕ)
    (β : Cocycle ℚ (TopCat.toSSet.obj Y) q)
    (α : Cohomology ℚ (TopCat.of ↥(A ∩ B)) 0) :
    mvδ Y A B hA hB hc q
      (cup (TopCat.of ↥(A ∩ B)) (Nat.add_zero q)
        (cohomologyMap ℚ q (topologicalSubsetInclusion Y (A ∩ B)) (cohomologyClass Y q β)) α) =
    (-1 : ℚ) ^ q • cup Y rfl (cohomologyClass Y q β) (mvδ Y A B hA hB hc 0 α) := by
  have hm := mvδ_operation leftOperation Y A B hA hB hc 0 q q (Nat.zero_add q) β
  rw [leftCupHomology_eq, leftCupHomology_eq] at hm
  have hclass := cohomologyMap_class Y (topologicalSubsetInclusion Y (A ∩ B)) q β
    (pullCocycle (TopCat.toSSet.map (topologicalSubsetInclusion Y (A ∩ B))) q β) rfl
  rw [← hclass] at hm
  have he := ConcreteCategory.congr_hom hm α
  simp only [Nat.mul_zero, pow_zero, one_smul, Nat.mul_one,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.smul_apply] at he
  rw [show q * (0 + 1) = q by omega] at he
  exact he

#print axioms mvδ_cup_left_zero
#print axioms mvδ_cup_right
end HodgeLean.Foundations.Singular

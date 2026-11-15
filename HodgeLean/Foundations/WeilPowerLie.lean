import HodgeLean.Foundations.WeilPower

/-! # The complex special unitary Lie algebra in Weil coordinates

This is the Lie-algebra part of F-1575's transport at the level of `⋀ H¹`.
It does not supply the Hodge-group input, C7, or algebraicity of generators.
Relation to the goal: HC no distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
namespace HodgeLean.Foundations.WeilPower
open SchurWeyl
variable (W : Type*) [AddCommGroup W] [Module ℂ W]

/-- The vector plus contragredient representation.
Source: constructed here for the complex special unitary Lie algebra. -/
def blockLie : Module.End ℂ W →ₗ⁅ℂ⁆ Module.End ℂ (W × Module.Dual ℂ W) where
  toFun f := f.prodMap (dualLie ℂ W f)
  map_add' f g := by simp only [map_add, LinearMap.prodMap_add]
  map_smul' c f := by simp only [map_smul, LinearMap.prodMap_smul, RingHom.id_apply]
  map_lie' {f g} := by
    rw [(dualLie ℂ W).map_lie]
    ext x <;> simp [Ring.lie_def, LinearMap.prodMap_apply]

example (f : Module.End ℂ W) (x : W) (φ : Module.Dual ℂ W) :
    blockLie W f (x, φ) = (f x, -(φ ∘ₗ f)) := rfl

theorem blockLie_injective : Function.Injective (blockLie W) := by
  intro f g h
  ext x
  exact congrArg Prod.fst (LinearMap.congr_fun h (x, 0))

/-- The split symplectic pairing, with sign matching `E(x,y)` on `W × W'`.
Source: constructed here for the polarization in split coordinates. -/
def splitForm : LinearMap.BilinForm ℂ (W × Module.Dual ℂ W) :=
  LinearMap.mk₂ ℂ (fun x y => y.2 x.1 - x.2 y.1)
    (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring)

example (x : W) (φ : Module.Dual ℂ W) : splitForm W (x, 0) (0, φ) = φ x := by
  simp [splitForm]

/-- The Weil operator in split coordinates.
Source: constructed here for the two embeddings of `ℚ(√-3)`. -/
def splitJ : Module.End ℂ (W × Module.Dual ℂ W) :=
  (root • LinearMap.id).prodMap (-root • LinearMap.id)

example (x : W) (φ : Module.Dual ℂ W) : splitJ W (x, φ) = (root • x, -root • φ) := rfl

/-- The first diagonal block of an endomorphism in split coordinates.
Source: constructed here to state the trace-zero condition on `W`. -/
def firstBlock (X : Module.End ℂ (W × Module.Dual ℂ W)) : Module.End ℂ W :=
  LinearMap.fst ℂ W (Module.Dual ℂ W) ∘ₗ X ∘ₗ LinearMap.inl ℂ W (Module.Dual ℂ W)

@[simp] theorem firstBlock_blockLie (f : Module.End ℂ W) :
    firstBlock W (blockLie W f) = f := by ext x; rfl

example (f : Module.End ℂ W) : firstBlock W (blockLie W f) = f := firstBlock_blockLie W f

theorem blockLie_commutes (f : Module.End ℂ W) :
    (blockLie W f).comp (splitJ W) = (splitJ W).comp (blockLie W f) := by
  ext x <;> simp [blockLie, splitJ]

theorem blockLie_skew (f : Module.End ℂ W) (x y : W × Module.Dual ℂ W) :
    splitForm W (blockLie W f x) y = -splitForm W x (blockLie W f y) := by
  simp [splitForm, blockLie, dualLie_apply, LinearMap.dualMap_apply]
  ring

/-- Commutation and skewness force the contragredient block. -/
theorem eq_blockLie_of_commutes_skew (X : Module.End ℂ (W × Module.Dual ℂ W))
    (hc : X.comp (splitJ W) = (splitJ W).comp X)
    (hs : ∀ x y, splitForm W (X x) y = -splitForm W x (X y)) :
    X = blockLie W (firstBlock W X) := by
  have hleft (x : W) : (X (x, 0)).2 = 0 := by
    have h := congrArg Prod.snd (LinearMap.congr_fun hc (x, 0))
    change (X (root • x, -root • (0 : Module.Dual ℂ W))).2 =
      -root • (X (x, 0)).2 at h
    simp only [smul_zero] at h
    have he : (root • x, (0 : Module.Dual ℂ W)) = root • (x, 0) := by simp
    rw [he, map_smul, Prod.smul_snd] at h
    have hz : (2 * root) • (X (x, 0)).2 = 0 := by
      calc
        _ = root • (X (x, 0)).2 + root • (X (x, 0)).2 := by module
        _ = 0 := add_eq_zero_iff_eq_neg.mpr (by simpa only [neg_smul] using h)
    exact (smul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) root_ne_zero)
  have hright (φ : Module.Dual ℂ W) : (X (0, φ)).1 = 0 := by
    have h := congrArg Prod.fst (LinearMap.congr_fun hc (0, φ))
    change (X (root • (0 : W), -root • φ)).1 = root • (X (0, φ)).1 at h
    simp only [smul_zero] at h
    have he : ((0 : W), -root • φ) = -root • (0, φ) := by simp
    rw [he, map_smul, Prod.smul_fst] at h
    have hz : (2 * root) • (X (0, φ)).1 = 0 := by
      calc
        _ = root • (X (0, φ)).1 + root • (X (0, φ)).1 := by module
        _ = 0 := add_eq_zero_iff_eq_neg.mpr (by simpa only [neg_smul] using h.symm)
    exact (smul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) root_ne_zero)
  have hd (φ : Module.Dual ℂ W) : (X (0, φ)).2 =
      dualLie ℂ W (firstBlock W X) φ := by
    ext x
    have h := hs (x, 0) (0, φ)
    change (X (0, φ)).2 x = -φ ((X (x, 0)).1)
    simp only [splitForm, LinearMap.mk₂_apply, map_zero, sub_zero,
      LinearMap.zero_apply] at h
    linear_combination h
  apply LinearMap.ext
  rintro ⟨x, φ⟩
  have hz : (x, φ) = (x, 0) + (0, φ) := by simp
  rw [hz, map_add, map_add]
  apply Prod.ext
  · simp [blockLie, hright, firstBlock]
  · simp [blockLie, hleft, hd]

variable [FiniteDimensional ℂ W]

/-- The split special unitary Lie algebra, embedded in endomorphisms.
Source: constructed here; its defining conditions are proved in `mem_splitSU`. -/
def splitSU : LieSubalgebra ℂ (Module.End ℂ (W × Module.Dual ℂ W)) :=
  ((blockLie W).comp (slEnd ℂ W).incl).range

omit [FiniteDimensional ℂ W] in
theorem mem_splitSU (X : Module.End ℂ (W × Module.Dual ℂ W)) :
    X ∈ splitSU W ↔
      X.comp (splitJ W) = (splitJ W).comp X ∧
      (∀ x y, splitForm W (X x) y = -splitForm W x (X y)) ∧
      LinearMap.trace ℂ W (firstBlock W X) = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨blockLie_commutes W f, blockLie_skew W f, ?_⟩
    change LinearMap.trace ℂ W (firstBlock W (blockLie W f)) = 0
    rw [firstBlock_blockLie]
    exact mem_slEnd.mp f.property
  · rintro ⟨hc, hs, ht⟩
    refine ⟨⟨firstBlock W X, mem_slEnd.mpr ht⟩, ?_⟩
    exact (eq_blockLie_of_commutes_skew W X hc hs).symm

example (f : slEnd ℂ W) : blockLie W f ∈ splitSU W := ⟨f, rfl⟩

/-- Restriction to `W`, as a Lie isomorphism from the split special unitary algebra.
Source: constructed here for F-1575's complex unitary-to-special-linear identification. -/
def splitSUEquiv : splitSU W ≃ₗ⁅ℂ⁆ slEnd ℂ W :=
  (((blockLie W).comp (slEnd ℂ W).incl).equivRangeOfInjective
    ((blockLie_injective W).comp Subtype.val_injective)).symm

example (f : slEnd ℂ W) : splitSUEquiv W ⟨blockLie W f, ⟨f, rfl⟩⟩ = f :=
  (splitSUEquiv W).apply_symm_apply f

end HodgeLean.Foundations.WeilPower


noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct
namespace HodgeLean.Foundations.WeilPower
open SchurWeyl
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
variable (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
  (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
  (hskew : ∀ x y, E (J x) y = -E x (J y))

/-- The polarization identifies the complexification with a vector space plus its dual.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5–6. -/
def polarizedSplitting : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ]
    (Module.End.eigenspace (J.baseChange ℂ) root ×
      Module.Dual ℂ (Module.End.eigenspace (J.baseChange ℂ) root)) :=
  (splitting J hJ).symm.trans
    ((LinearEquiv.refl ℂ _).prodCongr (weilDuality E hE J hJ hskew))

theorem polarizedSplitting_symm_apply
    (x : Module.End.eigenspace (J.baseChange ℂ) root)
    (φ : Module.Dual ℂ (Module.End.eigenspace (J.baseChange ℂ) root)) :
    (polarizedSplitting E hE J hJ hskew).symm (x, φ) =
      (x : ℂ ⊗[ℚ] V) + (weilDuality E hE J hJ hskew).symm φ := rfl

example : Function.Bijective (polarizedSplitting E hE J hJ hskew) :=
  (polarizedSplitting E hE J hJ hskew).bijective

theorem polarizedSplitting_J (z : ℂ ⊗[ℚ] V) :
    polarizedSplitting E hE J hJ hskew (J.baseChange ℂ z) =
      splitJ _ (polarizedSplitting E hE J hJ hskew z) := by
  let e := polarizedSplitting E hE J hJ hskew
  obtain ⟨⟨x, φ⟩, rfl⟩ := e.symm.surjective z
  apply e.symm.injective
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  change J.baseChange ℂ ((x : ℂ ⊗[ℚ] V) + (weilDuality E hE J hJ hskew).symm φ) = _
  rw [map_add, Module.End.mem_eigenspace_iff.mp x.property,
    Module.End.mem_eigenspace_iff.mp ((weilDuality E hE J hJ hskew).symm φ).property]
  simp [e, splitJ, polarizedSplitting_symm_apply]

omit hE J hJ hskew [FiniteDimensional ℚ V] in
theorem alternating_baseChange_skew (hAlt : E.IsAlt) (x y : ℂ ⊗[ℚ] V) :
    E.baseChange ℂ x y = -E.baseChange ℂ y x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      simp only [LinearMap.BilinForm.baseChange_tmul]
      rw [← hAlt.neg_eq x y, neg_smul, neg_neg, mul_comm]
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz, neg_add_rev]; abel
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, neg_add_rev]; abel

theorem polarizedSplitting_form (hAlt : E.IsAlt) (z t : ℂ ⊗[ℚ] V) :
    E.baseChange ℂ z t = splitForm _ (polarizedSplitting E hE J hJ hskew z)
      (polarizedSplitting E hE J hJ hskew t) := by
  let e := polarizedSplitting E hE J hJ hskew
  obtain ⟨⟨x, φ⟩, rfl⟩ := e.symm.surjective z
  obtain ⟨⟨y, ψ⟩, rfl⟩ := e.symm.surjective t
  change E.baseChange ℂ (e.symm (x, φ)) (e.symm (y, ψ)) =
    splitForm _ (e (e.symm (x, φ))) (e (e.symm (y, ψ)))
  rw [e.apply_symm_apply, e.apply_symm_apply]
  dsimp only [e]
  rw [polarizedSplitting_symm_apply, polarizedSplitting_symm_apply]
  simp only [map_add, LinearMap.add_apply]
  rw [(weil_isotropic E J hskew).1 _ x.property _ y.property,
    (weil_isotropic E J hskew).2 _ ((weilDuality E hE J hJ hskew).symm φ).property
      _ ((weilDuality E hE J hJ hskew).symm ψ).property]
  rw [alternating_baseChange_skew E hAlt ((weilDuality E hE J hJ hskew).symm φ) y]
  have hφ := congrArg (fun f => f y) ((weilDuality E hE J hJ hskew).apply_symm_apply φ)
  have hψ := congrArg (fun f => f x) ((weilDuality E hE J hJ hskew).apply_symm_apply ψ)
  change E.baseChange ℂ y ((weilDuality E hE J hJ hskew).symm φ) = φ y at hφ
  change E.baseChange ℂ x ((weilDuality E hE J hJ hskew).symm ψ) = ψ x at hψ
  rw [hφ, hψ]
  simp [splitForm]
  ring

/-- The complex special unitary Lie algebra on `ℂ ⊗ V`, in polarized coordinates.
Its commutation, skewness, and trace characterization is `mem_complexSU`.
Source: constructed here for van Geemen, §5–6, using the polarized splitting. -/
def complexSU : LieSubalgebra ℂ (Module.End ℂ (ℂ ⊗[ℚ] V)) :=
  (splitSU (Module.End.eigenspace (J.baseChange ℂ) root)).map
    (polarizedSplitting E hE J hJ hskew).symm.lieConj.toLieHom

/-- Restriction identifies the complex special unitary Lie algebra with `sl(W)`.
Source: constructed here for F-1575's transport. -/
def complexSUEquiv : complexSU E hE J hJ hskew ≃ₗ⁅ℂ⁆
    slEnd ℂ (Module.End.eigenspace (J.baseChange ℂ) root) :=
  ((polarizedSplitting E hE J hJ hskew).symm.lieConj.lieSubalgebraMap
    (splitSU _)).symm.trans (splitSUEquiv _)

example : Function.Bijective (complexSUEquiv E hE J hJ hskew) :=
  (complexSUEquiv E hE J hJ hskew).bijective

example (X : splitSU (Module.End.eigenspace (J.baseChange ℂ) root)) :
    (polarizedSplitting E hE J hJ hskew).symm.lieConj X ∈ complexSU E hE J hJ hskew :=
  ⟨X, X.property, rfl⟩

theorem complexSUEquiv_symm_coe
    (f : slEnd ℂ (Module.End.eigenspace (J.baseChange ℂ) root)) :
    ((complexSUEquiv E hE J hJ hskew).symm f : Module.End ℂ (ℂ ⊗[ℚ] V)) =
      (polarizedSplitting E hE J hJ hskew).symm.conj (blockLie _ f) := rfl

/-- The unitary action becomes the vector plus contragredient action. -/
theorem complexSU_action (X : complexSU E hE J hJ hskew) (z : ℂ ⊗[ℚ] V) :
    polarizedSplitting E hE J hJ hskew (X.1 z) =
      blockLie _ (complexSUEquiv E hE J hJ hskew X)
        (polarizedSplitting E hE J hJ hskew z) := by
  obtain ⟨f, rfl⟩ := (complexSUEquiv E hE J hJ hskew).symm.surjective X
  change polarizedSplitting E hE J hJ hskew
      (((complexSUEquiv E hE J hJ hskew).symm f : complexSU E hE J hJ hskew).1 z) =
    blockLie _ ((complexSUEquiv E hE J hJ hskew)
      ((complexSUEquiv E hE J hJ hskew).symm f))
        (polarizedSplitting E hE J hJ hskew z)
  rw [(complexSUEquiv E hE J hJ hskew).apply_symm_apply, complexSUEquiv_symm_coe]
  simp

/-- Membership is exactly commutation with `J`, polarization skewness, and trace zero on `W`.
The first block is restriction to `W` whenever the commutation condition holds. -/
theorem mem_complexSU (hAlt : E.IsAlt) (X : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    X ∈ complexSU E hE J hJ hskew ↔
      X.comp (J.baseChange ℂ) = (J.baseChange ℂ).comp X ∧
      (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) ∧
      LinearMap.trace ℂ (Module.End.eigenspace (J.baseChange ℂ) root)
        (firstBlock _ ((polarizedSplitting E hE J hJ hskew).conj X)) = 0 := by
  let e := polarizedSplitting E hE J hJ hskew
  have hmem : X ∈ complexSU E hE J hJ hskew ↔ e.conj X ∈ splitSU _ := by
    constructor
    · rintro ⟨Y, hY, rfl⟩
      simpa [e] using hY
    · intro h
      exact ⟨e.conj X, h, by simp [e]⟩
  rw [hmem, mem_splitSU]
  have hJmodel : e.conj (J.baseChange ℂ) = splitJ _ := by
    apply LinearMap.ext
    intro z
    simpa [e] using polarizedSplitting_J E hE J hJ hskew (e.symm z)
  have hc : (e.conj X).comp (splitJ _) = (splitJ _).comp (e.conj X) ↔
      X.comp (J.baseChange ℂ) = (J.baseChange ℂ).comp X := by
    rw [← hJmodel, ← e.conj_comp, ← e.conj_comp]
    exact e.conj.injective.eq_iff
  rw [hc]
  constructor
  · rintro ⟨hc, hs, ht⟩
    refine ⟨hc, ?_, ht⟩
    intro x y
    have h := hs (e x) (e y)
    simpa [← polarizedSplitting_form E hE J hJ hskew hAlt, e] using h
  · rintro ⟨hc, hs, ht⟩
    refine ⟨hc, ?_, ht⟩
    intro x y
    have h := hs (e.symm x) (e.symm y)
    simpa [polarizedSplitting_form E hE J hJ hskew hAlt, e] using h

@[simp] theorem polarizedSplitting_pos
    (x : Module.End.eigenspace (J.baseChange ℂ) root) :
    polarizedSplitting E hE J hJ hskew x = (x, 0) := by
  simp [polarizedSplitting, splitting]

@[simp] theorem polarizedSplitting_neg
    (y : Module.End.eigenspace (J.baseChange ℂ) (-root)) :
    polarizedSplitting E hE J hJ hskew y = (0, weilDuality E hE J hJ hskew y) := by
  simp [polarizedSplitting, splitting]

/-- The Lie isomorphism is literally restriction to the positive eigenspace. -/
theorem complexSU_restrict (X : complexSU E hE J hJ hskew)
    (x : Module.End.eigenspace (J.baseChange ℂ) root) :
    X.1 x = (((complexSUEquiv E hE J hJ hskew X :
      Module.End ℂ (Module.End.eigenspace (J.baseChange ℂ) root)) x) : ℂ ⊗[ℚ] V) := by
  apply (polarizedSplitting E hE J hJ hskew).injective
  rw [complexSU_action, polarizedSplitting_pos, polarizedSplitting_pos]
  simp [blockLie]

/-- The negative eigenspace is stable under the complex special unitary algebra. -/
theorem complexSU_preserves_neg (X : complexSU E hE J hJ hskew)
    (y : Module.End.eigenspace (J.baseChange ℂ) (-root)) :
    X.1 y ∈ Module.End.eigenspace (J.baseChange ℂ) (-root) := by
  rw [Module.End.mem_eigenspace_iff]
  apply (polarizedSplitting E hE J hJ hskew).injective
  rw [polarizedSplitting_J, map_smul, complexSU_action, polarizedSplitting_neg]
  simp [blockLie, splitJ]

/-- Polarization carries the action on the negative eigenspace to the contragredient. -/
theorem complexSU_contragredient (X : complexSU E hE J hJ hskew)
    (y : Module.End.eigenspace (J.baseChange ℂ) (-root)) :
    weilDuality E hE J hJ hskew ⟨X.1 y, complexSU_preserves_neg E hE J hJ hskew X y⟩ =
      dualLie ℂ _ (complexSUEquiv E hE J hJ hskew X) (weilDuality E hE J hJ hskew y) := by
  have h := congrArg Prod.snd (complexSU_action E hE J hJ hskew X y)
  have hl := polarizedSplitting_neg E hE J hJ hskew
    ⟨X.1 y, complexSU_preserves_neg E hE J hJ hskew X y⟩
  change polarizedSplitting E hE J hJ hskew (X.1 y) = _ at hl
  rw [hl, polarizedSplitting_neg] at h
  exact h

end HodgeLean.Foundations.WeilPower

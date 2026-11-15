import HodgeLean.Foundations.Program.G32SelectedRealizationProjector
import HodgeLean.Adapters.GagaMaps
import HodgeLean.Foundations.Program.G32SelectedRealizationTorus
import HodgeLean.Foundations.Program.G32SelectedRealizationMaps
import HodgeLean.Foundations.Program.G32SelectedRealizationProjector

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program

theorem g32x_saturated_projector_scalar {L : Type} [AddCommGroup L]
    [Module.IsTorsionFree ℤ L] (f : L →ₗ[ℤ] L) (d : ℤ)
    (hf : ∀ x, f (f x) = d • f x) (x : L)
    (hx : x ∈ b63l_saturation f.range) : f x = d • x := by
  obtain ⟨n, hn, y, hy⟩ := hx
  have he : n • f x = n • (d • x) := by
    calc
      _ = f (n • x) := (f.map_smul n x).symm
      _ = f (f y) := congrArg f hy.symm
      _ = d • f y := hf y
      _ = d • (n • x) := congrArg (fun z ↦ d • z) hy
      _ = _ := smul_comm d n x
  have hz : n • (f x - d • x) = 0 := by rw [smul_sub, he, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hn)

theorem g32x_groupEnd_square (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ a : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ a • x))
    (x : b3_periodLattice ℂ C) :
    b4_groupEnd ℂ b4b_projectorCoeff (b4_groupEnd ℂ b4b_projectorCoeff x) =
      b4b_projectorDenominator • b4_groupEnd ℂ b4b_projectorCoeff x := by
  let ρ : Representation ℤ b4b_Group (b3_periodLattice ℂ C) :=
    { toFun := fun a ↦ (b4_latticeAct ℂ a).toIntLinearMap
      map_one' := by
        apply LinearMap.ext
        intro y
        change b4_latticeAct ℂ (C := C) (1 : b4b_Group) y = y
        rw [b4_latticeAct_one hG]
        rfl
      map_mul' := fun a b ↦ by
        apply LinearMap.ext
        intro y
        change b4_latticeAct ℂ (a * b) y = b4_latticeAct ℂ a (b4_latticeAct ℂ b y)
        rw [b4_latticeAct_mul hG]
        rfl }
  have hs : (b4_groupEnd ℂ (C := C) b4b_projectorCoeff).toIntLinearMap =
      ∑ a : b4b_Group, b4b_projectorCoeff a • ρ a := by
    ext y
    simp [b4_groupEnd, ρ]
  change ((b4_groupEnd ℂ (C := C) b4b_projectorCoeff).toIntLinearMap *
    (b4_groupEnd ℂ (C := C) b4b_projectorCoeff).toIntLinearMap) x =
      (b4b_projectorDenominator •
        (b4_groupEnd ℂ (C := C) b4b_projectorCoeff).toIntLinearMap) x
  rw [hs, g32x_representation_convolution]
  simp_rw [b63l_projector_convolution]
  simp only [Finset.smul_sum, smul_smul]

theorem g32x_saturated_projector_retraction {L : Type} [AddCommGroup L]
    [Module.IsTorsionFree ℤ L] (f : L →ₗ[ℤ] L) (d : ℤ)
    (hf : ∀ x, f (f x) = d • f x) :
    ∃ p : L →ₗ[ℤ] b63l_saturation f.range,
      (b63l_saturation f.range).subtype ∘ₗ p = f ∧
        ∀ x : b63l_saturation f.range, p x.val = d • x := by
  let p := f.codRestrict (b63l_saturation f.range)
    (fun x ↦ ⟨1, one_ne_zero, by simpa only [one_smul] using LinearMap.mem_range_self f x⟩)
  refine ⟨p, ?_, ?_⟩
  · rfl
  · intro x
    apply Subtype.ext
    exact g32x_saturated_projector_scalar f d hf x.val x.property

theorem g32x_isMonHom_pow (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    (u : X ⟶ X) [IsMonHom u] (n : ℕ) : IsMonHom (u ^ n) := by
  induction n with
  | zero => rw [pow_zero, Hom.one_def]; infer_instance
  | succ n ih =>
    letI := ih
    rw [pow_succ, Hom.mul_def]
    infer_instance

theorem g32x_marked_retraction
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (L M : Type) [AddCommGroup L] [AddCommGroup M]
    (eX : L ≃+ b2_abelianLattice X) (eY : M ≃+ b2_abelianLattice Y)
    (j : M →+ L) (p : L →+ M) (N : ℕ) (hpj : ∀ l, p (j l) = N • l)
    (i : Y ⟶ X) [IsMonHom i] (q : X ⟶ Y) [IsMonHom q]
    (hi : ∀ x l, abelianPeriodEquiv Y (homPullback i 1 x) (eY l) =
      abelianPeriodEquiv X x (eX (j l)))
    (hq : ∀ x l, abelianPeriodEquiv X (homPullback q 1 x) (eX l) =
      abelianPeriodEquiv Y x (eY (p l))) :
    i ≫ q = 𝟙 Y ^ N := by
  letI := g32x_isMonHom_pow Y (𝟙 Y) N
  let u : AbelianEnd Y := ⟨i ≫ q, inferInstance⟩
  let v : AbelianEnd Y := ⟨𝟙 Y ^ N, inferInstance⟩
  apply congrArg AbelianEnd.hom (spec_abelianEndAction_injective Y (a₁ := u) (a₂ := v) ?_)
  change homPullback (i ≫ q) 1 = homPullback (𝟙 Y ^ N) 1
  have hpow := spec_homPullback_zpow (𝟙 Y) (N : ℤ)
  rw [zpow_natCast, spec_homPullback_id] at hpow
  rw [spec_homPullback_comp, hpow]
  apply LinearMap.ext
  intro x
  apply (abelianPeriodEquiv Y).injective
  apply AddMonoidHom.ext
  intro m
  obtain ⟨l, rfl⟩ := eY.surjective m
  rw [LinearMap.comp_apply, hi, hq, hpj]
  simp [LinearMap.smul_apply, map_nsmul]

theorem g32x_range_comp_of_scalar_retraction {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (g : W →ₗ[K] V) (c : K) (hc : c ≠ 0)
    (hgf : g ∘ₗ f = c • LinearMap.id) :
    LinearMap.range (f ∘ₗ g) = LinearMap.range f := by
  apply le_antisymm (LinearMap.range_comp_le_range _ _) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨c⁻¹ • f x, ?_⟩
  have hx : g (f x) = c • x := LinearMap.congr_fun hgf x
  simp [LinearMap.comp_apply, hx, hc]

theorem g32x_modelOperator_period (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (x : HQ (b5_model Λ F hF Q) 1) (l : Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    abelianPeriodEquiv _ (b63g_modelOperator Λ F hF Q hQ φ x) (b5_periodEquiv Λ F hF Q hQ l) =
      abelianPeriodEquiv _ x (b5_periodEquiv Λ F hF Q hQ (φ l)) := by
  simp [b63g_modelOperator, b63g_dualOperator, b63g_precomp, b63g_modelMap]


theorem g32x_isMonHom_zpow (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    (u : X ⟶ X) [IsMonHom u] (n : ℤ) : IsMonHom (u ^ n) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using g32x_isMonHom_pow X u n
  | negSucc n =>
    rw [zpow_negSucc]
    letI := g32x_isMonHom_pow X u (n + 1)
    infer_instance

theorem g32x_isMonHom_groupRing (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    {Idx : Type} [Fintype Idx] (u : Idx → (X ⟶ X))
    (hu : ∀ a, IsMonHom (u a)) (n : Idx → ℤ) : IsMonHom (∏ a, u a ^ n a) := by
  classical
  have hs (s : Finset Idx) : IsMonHom (∏ a ∈ s, u a ^ n a) := by
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Hom.one_def]; infer_instance
    | @insert a s ha ih =>
      letI := hu a
      letI := g32x_isMonHom_zpow X (u a) (n a)
      letI := ih
      rw [Finset.prod_insert ha, Hom.mul_def]
      infer_instance
  exact hs Finset.univ

theorem g32x_homPullback_prod (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {Idx : Type} [Fintype Idx] (u : Idx → (X ⟶ X)) (n : Idx → ℤ) :
    homPullback (∏ a, u a ^ n a) 1 = ∑ a, (n a : ℚ) • homPullback (u a) 1 := by
  classical
  have hs (s : Finset Idx) : homPullback (∏ a ∈ s, u a ^ n a) 1 =
      ∑ a ∈ s, (n a : ℚ) • homPullback (u a) 1 := by
    induction s using Finset.induction_on with
    | empty => simp [spec_homPullback_one]
    | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha,
        spec_homPullback_mul, spec_homPullback_zpow, ih]
  exact hs Finset.univ

theorem g32x_homPullback_pow (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (u : X ⟶ X) (n : ℕ) :
    homPullback (u ^ n) 1 = (n : ℚ) • homPullback u 1 := by
  have h := spec_homPullback_zpow u (n : ℤ)
  rw [zpow_natCast, Int.cast_natCast] at h
  exact h

theorem g32x_marked_comparison
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (L M : Type) [AddCommGroup L] [AddCommGroup M]
    (eX : L ≃+ b2_abelianLattice X) (eY : M ≃+ b2_abelianLattice Y)
    (FX : Submodule ℂ (ℂ ⊗[ℤ] L)) (FY : Submodule ℂ (ℂ ⊗[ℤ] M))
    (hFX : FX.map (b2_cplxMap eX.toAddMonoidHom) = b2_abelianF X)
    (hFY : FY.map (b2_cplxMap eY.toAddMonoidHom) = b2_abelianF Y)
    (j : M →+ L) (p : L →+ M)
    (hj : FY ≤ FX.comap (b2_cplxMap j)) (hp : FX ≤ FY.comap (b2_cplxMap p))
    (N : ℕ) (hpj : ∀ l, p (j l) = N • l) :
    ∃ i : Y ⟶ X, ∃ q : X ⟶ Y, IsMonHom i ∧ IsMonHom q ∧ i ≫ q = 𝟙 Y ^ N ∧
      ∀ x l, abelianPeriodEquiv X (homPullback (q ≫ i) 1 x) (eX l) =
        abelianPeriodEquiv X x (eX (j (p l))) := by
  obtain ⟨i, hiMon, hi⟩ := g32x_exists_marked_hom X Y M L eY eX FY FX hFY hFX j hj
  obtain ⟨q, hqMon, hq⟩ := g32x_exists_marked_hom Y X L M eX eY FX FY hFX hFY p hp
  letI := hiMon
  letI := hqMon
  have hret := g32x_marked_retraction X Y L M eX eY j p N hpj i q hi hq
  refine ⟨i, q, hiMon, hqMon, hret, ?_⟩
  intro x l
  rw [spec_homPullback_comp, LinearMap.comp_apply, hq, hi]


theorem g32y_over_hom_ext {Y X : Over (Spec ↧ℂ)} [IsReduced Y.left]
    [LocallyOfFiniteType Y.hom] [IsProjective X.hom] {f g : Y ⟶ X}
    (h : Point.map f = Point.map g) : f = g := by
  refine Over.OverMorphism.ext ?_
  have hf : f.left ≫ X.hom = Y.hom := Over.w f
  have hg : g.left ≫ X.hom = Y.hom := Over.w g
  have : LocallyOfFiniteType (f.left ≫ X.hom) := by rw [hf]; infer_instance
  refine ext_of_apply_eq (K := ℂ) X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ ?_
    (hf.trans hg.symm)
  intro x _ hx
  obtain ⟨a⟩ : Nonempty (Spec ↧ℂ) := inferInstance
  rw [← pointOfClosedPoint_apply Y.hom x hx a]
  have hh := congrArg (fun z => z.left)
    (congrFun h (Over.homMk (pointOfClosedPoint Y.hom x hx) (by simp) :
      Over.mk (𝟙 (Spec ↧ℂ)) ⟶ Y))
  change (pointOfClosedPoint Y.hom x hx ≫ f.left) a = (pointOfClosedPoint Y.hom x hx ≫ g.left) a
  exact congrArg (fun φ : Spec ↧ℂ ⟶ X.left => φ a) hh

theorem g32y_isMonHom_of_point_map_mul {Y X : Over (Spec ↧ℂ)} [GrpObj Y] [GrpObj X]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective X.hom] (h : Y ⟶ X)
    (hmul : ∀ x y : ComplexPoint Y, Point.map h (x * y) = Point.map h x * Point.map h y) :
    IsMonHom h := by
  have h1 : Point.map h 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact left_eq_mul.mp this
  let s : MonoidalCategory.tensorUnit (Over (Spec ↧ℂ)) ⟶ Over.mk (𝟙 (Spec ↧ℂ)) :=
    Over.homMk (MonoidalCategory.tensorUnit (Over (Spec ↧ℂ))).hom (by simp)
  have hs : s ≫ CartesianMonoidalCategory.toUnit _ = 𝟙 _ :=
    CartesianMonoidalCategory.toUnit_unique _ _
  have : IsIntegral (MonoidalCategory.tensorObj Y Y).left :=
    complexSelfProductIntegral_of_isIntegral Y
  have : LocallyOfFiniteType (MonoidalCategory.tensorObj Y Y).hom := by
    change LocallyOfFiniteType (Limits.pullback.fst Y.hom Y.hom ≫ Y.hom)
    infer_instance
  refine ⟨?_, ?_⟩
  · have h1' : (CartesianMonoidalCategory.toUnit _ ≫ η[Y]) ≫ h =
        CartesianMonoidalCategory.toUnit _ ≫ η[X] := h1
    calc η[Y] ≫ h = s ≫ (CartesianMonoidalCategory.toUnit _ ≫ η[Y]) ≫ h := by
          rw [Category.assoc, ← Category.assoc s, hs, Category.id_comp]
      _ = η[X] := by rw [h1', ← Category.assoc, hs, Category.id_comp]
  · apply g32y_over_hom_ext
    funext z
    change z ≫ μ ≫ h = z ≫ MonoidalCategory.tensorHom h h ≫ μ
    have hz : z = CartesianMonoidalCategory.lift (z ≫ CartesianMonoidalCategory.fst Y Y)
        (z ≫ CartesianMonoidalCategory.snd Y Y) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hz, ← Category.assoc, ← Category.assoc, CartesianMonoidalCategory.lift_map,
      ← Hom.mul_def, ← Hom.mul_def]
    exact hmul _ _


theorem g32y_algebraize_torus_map (X Y : Over (Spec ↧ℂ))
    [GrpObj X] [GrpObj Y] [IsIntegral X.left] [IsIntegral Y.left]
    [Smooth X.hom] [Smooth Y.hom] [IsProjective X.hom] [IsProjective Y.hom]
    (φ : b2_abelianLattice X →+ b2_abelianLattice Y)
    (hφ : b2_abelianF X ≤ (b2_abelianF Y).comap (b2_cplxMap φ)) :
    ∃ f : X ⟶ Y, IsMonHom f ∧ ∀ t,
      Point.map f (Additive.toMul (b2_abelianToPoint X t)) =
        Additive.toMul (b2_abelianToPoint Y (b2_torusHom _ _ φ hφ t)) := by
  classical
  let eX := AddEquiv.ofBijective (b2_abelianToPoint X) (b2_abelianToPoint_bijective X)
  let ψ : Additive (ComplexPoint X) →+ Additive (ComplexPoint Y) :=
    (b2_abelianToPoint Y).comp ((b2_torusHom _ _ φ hφ).comp eX.symm.toAddMonoidHom)
  let F : ComplexPoint X → ComplexPoint Y := fun x ↦ Additive.toMul (ψ (Additive.ofMul x))
  let := b2_latticeMap_discrete (b2_abelianF X) (b2_abelianF_isWeightOne X)
  let := b2_latticeMap_discrete (b2_abelianF Y) (b2_abelianF_isWeightOne Y)
  have hF : ContMDiff (modelWithCornersSelf ℂ (Fin (TopologicalSpace.dim X.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (TopologicalSpace.dim Y.left) → ℂ)) ω F :=
    (b2_abelianToPoint_contMDiff Y).comp
      ((b2_torusHom_contMDiff _ _ φ hφ).comp (b2_abelianToPoint_symm_contMDiff X))
  obtain ⟨f, hf⟩ := gagam_algebraize X Y F hF
  refine ⟨f, g32y_isMonHom_of_point_map_mul f ?_, ?_⟩
  · intro x y
    rw [hf]
    exact ψ.map_add (Additive.ofMul x) (Additive.ofMul y)
  · intro t
    rw [hf]
    change Additive.toMul (b2_abelianToPoint Y
      (b2_torusHom _ _ φ hφ (eX.symm (eX t)))) = _
    rw [eX.symm_apply_apply]

theorem g32y_lattice_retract_points (X Y : Over (Spec ↧ℂ))
    [GrpObj X] [GrpObj Y] [IsIntegral X.left] [IsIntegral Y.left]
    [Smooth X.hom] [Smooth Y.hom] [IsProjective X.hom] [IsProjective Y.hom]
    (f : AbelianEnd X)
    (iL : b2_abelianLattice Y →+ b2_abelianLattice X)
    (pL : b2_abelianLattice X →+ b2_abelianLattice Y)
    (hiL : b2_abelianF Y ≤ (b2_abelianF X).comap (b2_cplxMap iL))
    (hpL : b2_abelianF X ≤ (b2_abelianF Y).comap (b2_cplxMap pL))
    (N : ℕ) (hret : pL.comp iL = N • AddMonoidHom.id _)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l =
      abelianPeriod X x (iL (pL l))) :
    ∃ i : Y ⟶ X, ∃ q : X ⟶ Y,
      IsMonHom i ∧ IsMonHom q ∧ i ≫ q = 𝟙 Y ^ N ∧ q ≫ i = f.hom ∧
      (∀ t, Point.map i (Additive.toMul (b2_abelianToPoint Y t)) =
        Additive.toMul (b2_abelianToPoint X (b2_torusHom _ _ iL hiL t))) ∧
      ∀ t, Point.map q (Additive.toMul (b2_abelianToPoint X t)) =
        Additive.toMul (b2_abelianToPoint Y (b2_torusHom _ _ pL hpL t)) := by
  classical
  obtain ⟨i, hi, hipt⟩ := g32y_algebraize_torus_map Y X iL hiL
  obtain ⟨q, hq, hqpt⟩ := g32y_algebraize_torus_map X Y pL hpL
  have hiLpL : b2_abelianF X ≤ (b2_abelianF X).comap (b2_cplxMap (iL.comp pL)) := by
    have hc : b2_cplxMap (iL.comp pL) = b2_cplxMap iL ∘ₗ b2_cplxMap pL :=
      by
        ext
        rfl
    intro x hx
    change b2_cplxMap (iL.comp pL) x ∈ b2_abelianF X
    rw [hc, LinearMap.comp_apply]
    exact hiL (hpL hx)
  have hpLiL : b2_abelianF Y ≤ (b2_abelianF Y).comap (b2_cplxMap (pL.comp iL)) := by
    have hc : b2_cplxMap (pL.comp iL) = b2_cplxMap pL ∘ₗ b2_cplxMap iL :=
      by
        ext
        rfl
    intro x hx
    change b2_cplxMap (pL.comp iL) x ∈ b2_abelianF Y
    rw [hc, LinearMap.comp_apply]
    exact hpL (hiL hx)
  refine ⟨i, q, hi, hq, ?_, ?_, hipt, hqpt⟩
  · apply g32y_over_hom_ext
    funext y
    obtain ⟨t, rfl⟩ := b2_abelianToPoint_bijective Y |>.surjective (Additive.ofMul y)
    have hpow (y : ComplexPoint Y) : Point.map (𝟙 Y ^ N) y = y ^ N := by
      change y ≫ (𝟙 Y) ^ N = y ^ N
      rw [MonObj.comp_pow, Category.comp_id]
    change Point.map q (Point.map i (Additive.toMul (b2_abelianToPoint Y t))) =
      Point.map (𝟙 Y ^ N) (Additive.toMul (b2_abelianToPoint Y t))
    rw [hipt, hqpt, hpow, g32y_torusHom_comp _ _ _ iL pL hiL hpL hpLiL]
    have hs : ∀ t, b2_torusHom _ _ (pL.comp iL) hpLiL t = N • t := by
      have hscalar : b2_abelianF Y ≤ (b2_abelianF Y).comap
          (b2_cplxMap (N • AddMonoidHom.id (b2_abelianLattice Y))) := hret ▸ hpLiL
      intro t
      simpa only [hret] using (g32y_torusHom_nsmul (b2_abelianF Y) N hscalar t)
    rw [hs]
    exact (b2_abelianToPoint Y).map_nsmul N t
  · apply g32y_over_hom_ext
    funext x
    obtain ⟨t, rfl⟩ := b2_abelianToPoint_bijective X |>.surjective (Additive.ofMul x)
    change Point.map i (Point.map q (Additive.toMul (b2_abelianToPoint X t))) =
      Point.map f.hom (Additive.toMul (b2_abelianToPoint X t))
    rw [hqpt, hipt, g32y_torusHom_comp _ _ _ pL iL hpL hiL hiLpL]
    exact b2_abelianEnd_torusHom X f (iL.comp pL) hφ hiLpL t

theorem g32y_lattice_retract (X Y : Over (Spec ↧ℂ))
    [GrpObj X] [GrpObj Y] [IsIntegral X.left] [IsIntegral Y.left]
    [Smooth X.hom] [Smooth Y.hom] [IsProjective X.hom] [IsProjective Y.hom]
    (f : AbelianEnd X)
    (iL : b2_abelianLattice Y →+ b2_abelianLattice X)
    (pL : b2_abelianLattice X →+ b2_abelianLattice Y)
    (hiL : b2_abelianF Y ≤ (b2_abelianF X).comap (b2_cplxMap iL))
    (hpL : b2_abelianF X ≤ (b2_abelianF Y).comap (b2_cplxMap pL))
    (N : ℕ) (hret : pL.comp iL = N • AddMonoidHom.id _)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l =
      abelianPeriod X x (iL (pL l))) :
    ∃ i : Y ⟶ X, ∃ q : X ⟶ Y,
      IsMonHom i ∧ IsMonHom q ∧ i ≫ q = 𝟙 Y ^ N ∧ q ≫ i = f.hom := by
  obtain ⟨i, q, hi, hq, hr, hqi, _, _⟩ :=
    g32y_lattice_retract_points X Y f iL pL hiL hpL N hret hφ
  exact ⟨i, q, hi, hq, hr, hqi⟩

end HodgeLean.Foundations.Program

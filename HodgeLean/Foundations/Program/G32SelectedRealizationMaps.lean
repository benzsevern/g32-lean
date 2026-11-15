import HodgeLean.Foundations.Program.G32SelectedRealizationDefs

noncomputable section
open AlgebraicTopology.Singular
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program

theorem g32x_over_hom_ext (X : Over (Spec ↧ℂ)) [IsProjective X.hom] {Y : Over (Spec ↧ℂ)} [IsReduced Y.left]
    [LocallyOfFiniteType Y.hom] {f g : Y ⟶ X} (h : Point.map f = Point.map g) : f = g := by
  refine Over.OverMorphism.ext ?_
  have hf : f.left ≫ X.hom = Y.hom := Over.w f
  have hg : g.left ≫ X.hom = Y.hom := Over.w g
  have : LocallyOfFiniteType (f.left ≫ X.hom) := by rw [hf]; infer_instance
  refine ext_of_apply_eq (K := ℂ) X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ ?_
    (hf.trans hg.symm)
  intro x _ hx
  obtain ⟨a⟩ : Nonempty (Spec ↧ℂ) := inferInstance
  rw [← pointOfClosedPoint_apply Y.hom x hx a]
  have := congrArg (fun z => z.left)
    (congrFun h (Over.homMk (pointOfClosedPoint Y.hom x hx) (by simp) :
      Over.mk (𝟙 (Spec ↧ℂ)) ⟶ Y))
  change (pointOfClosedPoint Y.hom x hx ≫ f.left) a = (pointOfClosedPoint Y.hom x hx ≫ g.left) a
  exact congrArg (fun φ : Spec ↧ℂ ⟶ X.left => φ a) this

theorem g32x_isMonHom_of_pointMap_mul
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [IsProjective X.hom] [GrpObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : Y ⟶ X)
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
  · apply g32x_over_hom_ext X
    funext z
    change z ≫ μ ≫ h = z ≫ MonoidalCategory.tensorHom h h ≫ μ
    have hz : z = CartesianMonoidalCategory.lift (z ≫ CartesianMonoidalCategory.fst Y Y)
        (z ≫ CartesianMonoidalCategory.snd Y Y) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hz, ← Category.assoc, ← Category.assoc, CartesianMonoidalCategory.lift_map,
      ← Hom.mul_def, ← Hom.mul_def]
    exact hmul _ _

theorem g32x_exists_hom_of_lattice
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ l ∈ abelianPeriodLattice Y, A l ∈ abelianPeriodLattice X) :
    ∃ f : Y ⟶ X, IsMonHom f ∧ ∀ v,
      Additive.toMul (complexExponential X (dim X.left) (A v)) =
        Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v)) := by
  have hhol : ContMDiff 𝓘(ℂ, Fin (dim Y.left) → ℂ)
      𝓘(ℂ, Fin (dim X.left) → ℂ) ω A :=
    (LinearMap.toContinuousLinearMap A).contMDiff
  obtain ⟨F, ⟨hFhol, hF⟩, _⟩ :=
    spec_existsUnique_contMDiff_descent_manifold Y (dim Y.left)
      𝓘(ℂ, Fin (dim X.left) → ℂ)
      (fun v ↦ Additive.toMul (complexExponential X (dim X.left) (A v)))
      ((spec_contMDiff_complexExponential X (dim X.left)).comp hhol)
      (fun l hl v ↦ by
        have h0 : complexExponential X (dim X.left) (A l) = 0 := hA l hl
        change Additive.toMul (complexExponentialHom X (dim X.left) (A (v + l))) = _
        rw [map_add, map_add]
        change Additive.toMul (_ + complexExponential X (dim X.left) (A l)) = _
        rw [h0, add_zero]
        rfl)
  obtain ⟨f, rfl⟩ := gagam_algebraize Y X F hFhol
  refine ⟨f, g32x_isMonHom_of_pointMap_mul X Y f ?_, fun v ↦ (hF v).symm⟩
  intro x y
  obtain ⟨v, hv⟩ := surjective_complexExponential Y (dim Y.left) (Additive.ofMul x)
  obtain ⟨w, hw⟩ := surjective_complexExponential Y (dim Y.left) (Additive.ofMul y)
  have hx : x = Additive.toMul (complexExponential Y (dim Y.left) v) := by rw [hv]; rfl
  have hy : y = Additive.toMul (complexExponential Y (dim Y.left) w) := by rw [hw]; rfl
  have hexpY (a b : Fin (dim Y.left) → ℂ) :
      Additive.toMul (complexExponential Y (dim Y.left) (a + b)) =
        Additive.toMul (complexExponential Y (dim Y.left) a) *
          Additive.toMul (complexExponential Y (dim Y.left) b) :=
    congrArg Additive.toMul ((complexExponentialHom Y (dim Y.left)).map_add a b)
  rw [hx, hy, ← hexpY, hF, hF, hF, map_add]
  exact congrArg Additive.toMul ((complexExponentialHom X (dim X.left)).map_add _ _)

theorem g32x_homPullback_period_of_analytic
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ X)
    (A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v)))
    (φ : abelianPeriodLattice Y →+ abelianPeriodLattice X)
    (hφ : ∀ l : abelianPeriodLattice Y, A l = φ l) (x : HQ X 1) (l : abelianPeriodLattice Y) :
    abelianPeriod Y (homPullback f 1 x) l = abelianPeriod X x (φ l) := by
  have hloop : (Point.continuousMap f).comp (abelianLatticeLoop Y l) =
      abelianLatticeLoop X (φ l) := by
    apply ContinuousMap.ext
    intro z
    induction z using QuotientAddGroup.induction_on with
    | H t =>
      change Point.map f (Additive.toMul (oneParameterSubgroup Y (dim Y.left)
          (l : Fin (dim Y.left) → ℂ) t)) =
        Additive.toMul (oneParameterSubgroup X (dim X.left)
          (φ l : Fin (dim X.left) → ℂ) t)
      rw [← complexExponential_smul, ← complexExponential_smul, ← hA,
        LinearMap.map_smul_of_tower, hφ]
  have hc : cupComparison Y 1 (homPullback f 1 x) =
      cohomologyMap ℚ 1 (TopCat.ofHom (Point.continuousMap f)) (cupComparison X 1 x) := by
    simp [homPullback]
  change loopPeriod (abelianLatticeLoop Y l) (cupComparison Y 1 (homPullback f 1 x)) =
    loopPeriod (abelianLatticeLoop X (φ l)) (cupComparison X 1 x)
  rw [hc, ← loopPeriod_comp, hloop]

theorem g32x_exists_hom_of_filtration
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (φ : b2_abelianLattice Y →+ b2_abelianLattice X)
    (hφ : b2_abelianF Y ≤ (b2_abelianF X).comap (b2_cplxMap φ)) :
    ∃ f : Y ⟶ X, IsMonHom f ∧ ∀ x l,
      abelianPeriod Y (homPullback f 1 x) l = abelianPeriod X x (φ l) := by
  let eX := b2a_evalEquiv X
  let eY := b2a_evalEquiv Y
  let A := eX.toLinearMap ∘ₗ
    (b2_abelianF Y).mapQ (b2_abelianF X) (b2_cplxMap φ) hφ ∘ₗ eY.symm.toLinearMap
  have heX (l : b2_abelianLattice X) :
      eX (Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℤ] l)) = l := by
    change b2_abelianEval X ((1 : ℂ) ⊗ₜ[ℤ] l) = _
    simp [b2_abelianEval]
  have heY (l : b2_abelianLattice Y) :
      eY (Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℤ] l)) = l := by
    change b2_abelianEval Y ((1 : ℂ) ⊗ₜ[ℤ] l) = _
    simp [b2_abelianEval]
  have hA (l : b2_abelianLattice Y) : A l = φ l := by
    rw [← heY l]
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    change eX (Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℤ] φ l)) = _
    exact heX _
  obtain ⟨f, hmon, hf⟩ := g32x_exists_hom_of_lattice X Y A
    (fun l hl ↦ by rw [hA ⟨l, hl⟩]; exact (φ ⟨l, hl⟩).property)
  exact ⟨f, hmon, g32x_homPullback_period_of_analytic X Y f A hf φ hA⟩

theorem g32x_exists_marked_hom
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (L M : Type) [AddCommGroup L] [AddCommGroup M]
    (eY : L ≃+ b2_abelianLattice Y) (eX : M ≃+ b2_abelianLattice X)
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) (G : Submodule ℂ (ℂ ⊗[ℤ] M))
    (hFY : F.map (b2_cplxMap eY.toAddMonoidHom) = b2_abelianF Y)
    (hGX : G.map (b2_cplxMap eX.toAddMonoidHom) = b2_abelianF X)
    (φ : L →+ M) (hφ : F ≤ G.comap (b2_cplxMap φ)) :
    ∃ f : Y ⟶ X, IsMonHom f ∧ ∀ x l,
      abelianPeriodEquiv Y (homPullback f 1 x) (eY l) =
        abelianPeriodEquiv X x (eX (φ l)) := by
  let χ := eX.toAddMonoidHom.comp (φ.comp eY.symm.toAddMonoidHom)
  have hχ : b2_abelianF Y ≤ (b2_abelianF X).comap (b2_cplxMap χ) := by
    rw [← hFY, ← hGX]
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨b2_cplxMap φ w, hφ hw, ?_⟩
    have he : χ.comp eY.toAddMonoidHom = eX.toAddMonoidHom.comp φ := by
      ext l
      simp [χ]
    change b2_cplxMap eX.toAddMonoidHom (b2_cplxMap φ w) =
      b2_cplxMap χ (b2_cplxMap eY.toAddMonoidHom w)
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← b63g_cplxMap_comp, ← b63g_cplxMap_comp, he]
  obtain ⟨f, hmon, hf⟩ := g32x_exists_hom_of_filtration X Y χ hχ
  refine ⟨f, hmon, fun x l ↦ ?_⟩
  have hY := Classical.choose_spec (spec_abelianPeriod_equiv Y)
  have hX := Classical.choose_spec (spec_abelianPeriod_equiv X)
  exact (hY _ _).trans ((hf x (eY l)).trans (by
    rw [show χ (eY l) = eX (φ l) by simp [χ]]
    exact (hX x (eX (φ l))).symm))

end HodgeLean.Foundations.Program

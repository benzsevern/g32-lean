import HodgeLean.Foundations.Program.SchoenTowerI2bTransport
import HodgeLean.Adapters.AbelianPowerProofs
import HodgeLean.Foundations.Program.SchoenCycleGeometryChecks

/-! Checked generic-source suppliers for the retained tower.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A locally free rank-one pulled-back ideal has proper support on an integral source.
Source: Hartshorne, Algebraic Geometry, II.6, effective Cartier divisors. -/
theorem s2v_cartier_pullback_support_ne_top {X Y : Scheme}
    [IsIntegral X] (f : X ⟶ Y) (I : Y.IdealSheafData)
    (hcartier : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap f).ideal U) ≃ₗ[Γ(X, U.1)] Γ(X, U.1))) :
    (I.comap f).support ≠ ⊤ := by
  intro hs
  have hi : I.comap f = ⊥ := Scheme.IdealSheafData.support_eq_top_iff.mp hs
  obtain ⟨U, hx, ⟨e⟩⟩ := hcartier (genericPoint X)
  letI : Nonempty U.1 := ⟨⟨genericPoint X, hx⟩⟩
  have hz : (I.comap f).ideal U = ⊥ := by rw [hi]; rfl
  haveI : Subsingleton ((I.comap f).ideal U) := by rw [hz]; infer_instance
  haveI : Subsingleton Γ(X, U.1) := e.symm.injective.subsingleton
  exact (zero_ne_one : (0 : Γ(X, U.1)) ≠ 1) (Subsingleton.elim _ _)

/-- A dominant field-valued source avoids every proper ideal support.
Source: Hartshorne, Algebraic Geometry, II.3, generic points and ideal support. -/
theorem s2v_dominant_fieldSource_comap_eq_top {L : Type} [Field L]
    {Y : Scheme} (f : Spec (CommRingCat.of L) ⟶ Y) [IsDominant f]
    (I : Y.IdealSheafData) (hI : I.support ≠ ⊤) : I.comap f = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hmem : f x ∈ I.support := by
    change x ∈ ((I.comap f).support : Set (Spec (CommRingCat.of L))) at hx
    rw [Scheme.IdealSheafData.support_comap] at hx
    exact hx
  have hr : Set.range f ⊆ I.support := by
    rintro y ⟨z, rfl⟩
    exact (Subsingleton.elim x z) ▸ hmem
  have hall : (Set.univ : Set Y) ⊆ I.support := by
    rw [← f.denseRange.closure_range]
    exact closure_minimal hr I.support.isClosed
  exact (hI (top_unique hall)).elim

/-- The retained blowup property uniquely determines a lift of a dominant field-valued map.
Source: Hartshorne, Algebraic Geometry, II.7, the blowup universal property. -/
theorem s2v_blowup_fieldSource_lift_unique {L : Type} [Field L]
    {B Bnext : Over (Spec ↧ℂ)} (b : Bnext ⟶ B) (I : B.left.IdealSheafData)
    (hI : I.support ≠ ⊤)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U.1)] Γ(T.left, U.1))) →
      ∃! u : T ⟶ Bnext, u ≫ b = f)
    (f : Spec (CommRingCat.of L) ⟶ B.left) [IsDominant f]
    (v w : Spec (CommRingCat.of L) ⟶ Bnext.left)
    (hv : v ≫ b.left = f) (hw : w ≫ b.left = f) : v = w := by
  let T : Over (Spec ↧ℂ) := Over.mk (f ≫ B.hom)
  let fO : T ⟶ B := Over.homMk f rfl
  haveI : IsAffine T.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of L)))
  have hunit : I.comap f = ⊤ := s2v_dominant_fieldSource_comap_eq_top f I hI
  obtain ⟨u, hu, huniq⟩ := hblowup T fO (by
    intro x
    refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_⟩
    refine ⟨(LinearEquiv.ofEq _ _ ?_).trans Submodule.topEquiv⟩
    change (I.comap f).ideal ⟨⊤, isAffineOpen_top _⟩ = ⊤
    rw [hunit]
    rfl)
  let vO : T ⟶ Bnext := Over.homMk v (by
    change v ≫ Bnext.hom = f ≫ B.hom
    rw [← b.w, ← Category.assoc, hv])
  let wO : T ⟶ Bnext := Over.homMk w (by
    change w ≫ Bnext.hom = f ≫ B.hom
    rw [← b.w, ← Category.assoc, hw])
  have hvO : vO ≫ b = fO := Over.OverMorphism.ext hv
  have hwO : wO ≫ b = fO := Over.OverMorphism.ext hw
  exact congrArg Over.Hom.left ((huniq vO hvO).trans (huniq wO hwO).symm)

/-- Surjectivity on complex points is preserved by the actual finite scheme powers.
Source: the universal property of the iterated scheme product. -/
theorem s2v_powerMap_points_surjective {Y Z : Over (Spec ↧ℂ)} (p : Y ⟶ Z)
    (hp : Function.Surjective (Point.map p)) (h : ℕ) :
    Function.Surjective (Point.map (s2_powerMap p h)) := by
  intro z
  choose y hy using fun i : Fin h => hp (Point.map (g3_proj Z h i) z)
  refine ⟨s2_lift h y, ?_⟩
  obtain ⟨hlim⟩ := spec_g3_isLimit_fan_aux Z h
  apply Fan.IsLimit.hom_ext hlim
  intro i
  change (s2_lift h y ≫ s2_powerMap p h) ≫ g3_proj Z h i = z ≫ g3_proj Z h i
  rw [Category.assoc, s2_powerMap, s2_check_lift_proj, ← Category.assoc, s2_check_lift_proj]
  exact hy i

/-- Surjectivity on complex points forces dominance over a finite-type complex base.
Source: Hartshorne, Algebraic Geometry, II.3, the density of closed points. -/
theorem s2v_dominant_of_points_surjective {X Y : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    (hf : Function.Surjective (Point.map f)) : IsDominant f.left := by
  letI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hr : closedPoints Y.left ⊆ Set.range f.left := by
    intro y hy
    let z : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y hy) (by simp)
    obtain ⟨x, hx⟩ := hf z
    refine ⟨x.left (IsLocalRing.closedPoint ℂ), ?_⟩
    have he := congrArg (fun t : ComplexPoint Y => t.left (IsLocalRing.closedPoint ℂ)) hx
    change f.left (x.left (IsLocalRing.closedPoint ℂ)) =
      pointOfClosedPoint Y.hom y hy (IsLocalRing.closedPoint ℂ) at he
    rw [pointOfClosedPoint_apply] at he
    exact he
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← closure_closedPoints (X := Y.left)]
  exact closure_mono hr

/-- The actual original covering map is surjective on complex points.
Source: Schoen (1988), §1, the quotient square for the curve power. -/
theorem s2v_originalCover_points_surjective
    {Y Z W B : Over (Spec ↧ℂ)} (p : Y ⟶ Z)
    (hp : Function.Surjective (Point.map p)) (h : ℕ)
    (q : g3_power Y h ⟶ W) (γ : g3_power Z h ⟶ B)
    (hγ : Function.Surjective (Point.map γ)) (β : W ⟶ B)
    (hβ : q ≫ β = s2_powerMap p h ≫ γ) :
    Function.Surjective (Point.map β) := by
  intro b
  obtain ⟨z, rfl⟩ := hγ b
  obtain ⟨y, rfl⟩ := s2v_powerMap_points_surjective p hp h z
  refine ⟨Point.map q y, ?_⟩
  change (y ≫ q) ≫ β = (y ≫ s2_powerMap p h) ≫ γ
  rw [Category.assoc, hβ, Category.assoc]

/-- The generic-source morphism of an integral scheme is dominant.
Source: Hartshorne, Algebraic Geometry, II.3, the generic point of an integral scheme. -/
theorem s2v_fromSpecFunctionField_dominant (X : Scheme) [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← genericPoint_closure (α := X)]
  apply closure_mono
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact ⟨IsLocalRing.closedPoint X.functionField, X.fromSpecStalk_closedPoint⟩

/-- The retained initial generic-source map is dominant by its actual quotient square.
Source: Schoen (1988), §1, the initial cover and its function field. -/
theorem s2v_initial_genericSource_dominant
    {Y Z W B Binit : Over (Spec ↧ℂ)} [IsIntegral W.left]
    [LocallyOfFiniteType B.hom] (p : Y ⟶ Z)
    (hp : Function.Surjective (Point.map p)) (h : ℕ)
    (q : g3_power Y h ⟶ W) (γ : g3_power Z h ⟶ B)
    (hγ : Function.Surjective (Point.map γ)) (β : W ⟶ B)
    (hβ : q ≫ β = s2_powerMap p h ≫ γ)
    (e : Binit ≅ B) (η : Spec W.left.functionField ⟶ Binit.left)
    (hη : η ≫ e.hom.left = W.left.fromSpecStalk (genericPoint W.left) ≫ β.left) :
    IsDominant η := by
  haveI : IsDominant β.left := s2v_dominant_of_points_surjective β
    (s2v_originalCover_points_surjective p hp h q γ hγ β hβ)
  haveI : IsDominant (W.left.fromSpecStalk (genericPoint W.left)) :=
    s2v_fromSpecFunctionField_dominant W.left
  haveI : IsDominant (η ≫ e.hom.left) := by rw [hη]; infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion η e.hom.left

end HodgeLean.Foundations.Program

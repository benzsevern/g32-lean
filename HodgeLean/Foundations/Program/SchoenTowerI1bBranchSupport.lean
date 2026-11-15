import HodgeLean.Foundations.Program.SchoenTowerI1bTranslations

/-! # I1b branch-support lifts
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- A complex point in the scheme image of a proper map lifts to a complex point.
Source: Hartshorne, Algebraic Geometry, II.4 and II.3, proper images and closed points. -/
theorem s2v_point_lift_of_mem_proper_image {X Y : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (y : ComplexPoint Y)
    (hy : y.left (IsLocalRing.closedPoint ℂ) ∈ f.left.ker.support) :
    ∃ x : ComplexPoint X, Point.map f x = y := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hr : y.left (IsLocalRing.closedPoint ℂ) ∈ Set.range f.left := by
    change y.left (IsLocalRing.closedPoint ℂ) ∈ (f.left.ker.support : Set Y.left) at hy
    rw [Scheme.Hom.support_ker, f.left.isClosedMap.isClosed_range.closure_eq] at hy
    exact hy
  have hyc : IsClosed ({y.left (IsLocalRing.closedPoint ℂ)} : Set Y.left) :=
    (pointEquivClosedPoint Y.hom ⟨y.left, by simpa using y.w⟩).property
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (Z := f.left ⁻¹' {y.left (IsLocalRing.closedPoint ℂ)})
    (by obtain ⟨z, hz⟩ := hr; exact ⟨z, hz⟩)
    (hyc.preimage f.left.continuous).isLocallyClosed
  let x : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom z hzc) (by simp)
  refine ⟨x, ?_⟩
  apply Over.OverMorphism.ext
  apply ext_of_apply_closedPoint_eq Y.hom
  · simpa using (Point.map f x).w
  · simpa using y.w
  · change f.left (pointOfClosedPoint X.hom z hzc (IsLocalRing.closedPoint ℂ)) = _
    rw [pointOfClosedPoint_apply]
    exact hz

/-- A complex point of the specified branch ideal has a retained insertion preimage.
Source: Schoen (1988), §2, p. 12, the divisor defined by insertion of a branch point. -/
theorem s2v_branchIdeal_support_point_lift
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom] [IsProjective B.hom]
    (h : ℕ) (γ : g3_power Z (h + 1) ⟶ B) (b : ComplexPoint Z)
    (z : ComplexPoint B)
    (hz : z.left (IsLocalRing.closedPoint ℂ) ∈ (s2c_branchIdeal Z B h γ b).support) :
    ∃ u : ComplexPoint (g3_power Z h),
      Point.map (s2c_branchInsertion Z h b ≫ γ) u = z := by
  let f := s2c_branchInsertion Z h b ≫ γ
  haveI : IsProper (f.left ≫ B.hom) := by
    rw [f.w]
    infer_instance
  haveI : IsProper f.left := IsProper.of_comp f.left B.hom
  exact s2v_point_lift_of_mem_proper_image f z hz

/-- A branch-insertion tuple lifts with its first coordinate equal to the chosen curve point.
Source: Schoen (1988), §2, p. 12, coordinatewise lifting through the curve cover. -/
theorem s2v_branchInsertion_lift_with_coordinate {Y Z : Over (Spec ↧ℂ)}
    (p : Y ⟶ Z) (hp : Function.Surjective (Point.map p))
    (h : ℕ) (y : ComplexPoint Y) (z : ComplexPoint (g3_power Z h)) :
    ∃ x : ComplexPoint (g3_power Y (h + 1)),
      Point.map (g3_proj Y (h + 1) 0) x = y ∧
      Point.map (s2_powerMap p (h + 1)) x =
        Point.map (s2c_branchInsertion Z h (Point.map p y)) z := by
  choose v hv using fun i : Fin h => hp (Point.map (g3_proj Z h i) z)
  let x : ComplexPoint (g3_power Y (h + 1)) := s2_lift (h + 1) (Fin.cases y v)
  refine ⟨x, ?_, ?_⟩
  · change s2_lift (h + 1) (Fin.cases y v) ≫ g3_proj Y (h + 1) 0 = y
    rw [s2_check_lift_proj]
    rfl
  · obtain ⟨hlim⟩ := spec_g3_isLimit_fan_aux Z (h + 1)
    apply Fan.IsLimit.hom_ext hlim
    intro i
    change (x ≫ s2_powerMap p (h + 1)) ≫ g3_proj Z (h + 1) i =
      (z ≫ s2c_branchInsertion Z h (Point.map p y)) ≫ g3_proj Z (h + 1) i
    rw [Category.assoc, s2_powerMap, s2_check_lift_proj, ← Category.assoc]
    change (s2_lift (h + 1) (Fin.cases y v) ≫ g3_proj Y (h + 1) i) ≫ p = _
    rw [s2_check_lift_proj, Category.assoc, s2c_branchInsertion, s2_check_lift_proj]
    refine Fin.cases ?_ (fun j => ?_) i
    · change y ≫ p = z ≫ CartesianMonoidalCategory.toUnit _ ≫ (y ≫ p)
      have hz : z ≫ CartesianMonoidalCategory.toUnit _ = 𝟙 _ := Subsingleton.elim _ _
      rw [← Category.assoc, hz, Category.id_comp]
    · exact hv j

/-- Every point of the original branch ideal has a covering point fixed by its exponent.
Source: Schoen (1988), §1, p. 5 and §2, p. 12, the quotient and branch insertion. -/
theorem s2v_branch_support_has_inertia_point
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsProjective Z.hom] [IsProjective B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z) (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (y : rsq_Quot S.χ.ker C) (rot : S.H ⧸ S.χ.ker) (n : ℕ)
    (hrot : b4_IsRotGen ℂ y rot ∧ e rot = Multiplicative.ofAdd (n : ZMod S.m))
    (h : ℕ) (hh : 0 < h + 1) (q : g3_power Y (h + 1) ⟶ W)
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m), ∑ i, v i = 0 →
      s2_action S Y a e (h + 1) v 1 ≫ q = q)
    (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q)
    (γ : g3_power Z (h + 1) ⟶ B) (β : W ⟶ B)
    (hβ : q ≫ β = s2_powerMap p (h + 1) ≫ γ)
    (z : ComplexPoint B)
    (hz : z.left (IsLocalRing.closedPoint ℂ) ∈
      (s2c_branchIdeal Z B h γ (Point.map p (eY y))).support) :
    ∃ w : ComplexPoint W, Point.map β w = z ∧ (Point.map d)^[n] w = w := by
  obtain ⟨u, hu⟩ := s2v_branchIdeal_support_point_lift Z B h γ (Point.map p (eY y)) z hz
  obtain ⟨x, hx0, hxp⟩ := s2v_branchInsertion_lift_with_coordinate p hpsurj h (eY y) u
  refine ⟨Point.map q x, ?_, ?_⟩
  · change (x ≫ q) ≫ β = z
    rw [Category.assoc, hβ, ← Category.assoc]
    change Point.map γ (Point.map (s2_powerMap p (h + 1)) x) = z
    rw [hxp]
    simpa only [Point.map, Category.assoc] using hu
  · apply s2v_branch_coordinate_quotient_inertia S Y Z W a e ha1 hamul p hporbit C eY
      hpointAction y rot n hrot (h + 1) hh q hqinv d hgenerator 0 x
    rw [hx0]


end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorUnbranchedResidue
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportOrderReduction
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportCharacterRoot
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportConstants
import HodgeLean.Foundations.Program.SchoenTowerL1bDeckOriginal
import HodgeLean.Foundations.Program.SchoenTowerL1bDeckGeneric
import HodgeLean.Foundations.Program.SchoenTowerL1bRotationStalkCharacter
import HodgeLean.Foundations.Program.SchoenTowerL1bKvalMaps
import HodgeLean.Foundations.Program.SchoenTowerInertiaSuppliers
import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerRoots
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerCancellation
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerRescaling
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerBranchRestriction
import HodgeLean.Foundations.Program.SchoenTowerL1bTowerGenerators
import HodgeLean.Foundations.Program.SchoenCycleFixedStalkScalars
import HodgeLean.Foundations.Program.SchoenTowerL1bKvalRamifiedFraction
import HodgeLean.Foundations.Program.SchoenTowerL1bLocalKummerEmbedding
import HodgeLean.Foundations.Program.SchoenTowerL1bClosedPrimeExpansion
import HodgeLean.Foundations.Program.SchoenTowerL1bLocalScalarSelection
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorPullbackResidue
import HodgeLean.Foundations.Program.SchoenTowerL1bEarlierMaps
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorQuotientOrders
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorEquationOfOrders
import HodgeLean.Foundations.Program.SchoenTowerL1bKvalFactorial
import HodgeLean.Foundations.Program.SchoenTowerL1bBranchEquations
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerInitial


noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff OnePoint Classical
namespace HodgeLean.Foundations.Program



theorem s2v_l1b_divisor_original_curve_aux
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p₀ : Y ⟶ Z) [IsFinite p₀.left]
    (hp₀ : ∀ u, a u ≫ p₀ = p₀)
    (hpsurj : Function.Surjective (Point.map p₀))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker)
    (hrot : ∀ t, b4_IsRotGen ℂ (y t) (rot t) ∧
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S).get (t) : ZMod S.m))
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t))))
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t)))
    (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S).get (t) ∧ (g32p_exponents S).get (t) < S.m)
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hcomparison :
    ∀ j : Fin (g32p_exponents S).length,
      let p := (eY (y j)).left (IsLocalRing.closedPoint ℂ)
      ∃ (hp : (a (rot j)).left p = p)
        (ι : Y.left.presheaf.stalk p →+* PowerSeries ℂ),
        Function.Injective ι ∧
        (∃ u : Y.left.presheaf.stalk p, ι u = PowerSeries.X) ∧
        (∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC p c) = PowerSeries.C c) ∧
        ∀ v : Y.left.presheaf.stalk p,
          ι (s2e_fixed_point_stalkPullback Y.left (a (rot j)).left p hp v) =
            PowerSeries.rescale
              (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) /
                (orderOf (rot j) : ℂ))) (ι v))
 :
    ∀ (κZ : Z.left.functionField ⟶ Y.left.functionField)
      (τY : Y.left.functionField ≃+* Y.left.functionField)
      (u : Y.left.functionField) (v : Z.left.functionField),
      Spec.map κZ ≫ Z.left.fromSpecStalk (genericPoint Z.left) =
        Y.left.fromSpecStalk (genericPoint Y.left) ≫ p₀.left →
      Spec.map (CommRingCat.ofHom τY.toRingHom) ≫
          Y.left.fromSpecStalk (genericPoint Y.left) =
        Y.left.fromSpecStalk (genericPoint Y.left) ≫
          (a (e.symm (Multiplicative.ofAdd (1 : ZMod S.m)))).left →
      u ≠ 0 → u ^ S.m = κZ.hom v →
      τY u = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
        Y.left.germToFunctionField ⊤).hom
          (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))) * u →
      ∀ (z₀ : ComplexPoint Z) (A B : Z.left.presheaf.stalk z₀.underlying),
        A ≠ 0 → B ≠ 0 →
        v = algebraMap (Z.left.presheaf.stalk z₀.underlying) Z.left.functionField A /
          algebraMap (Z.left.presheaf.stalk z₀.underlying) Z.left.functionField B →
        ∀ π : Z.left.presheaf.stalk z₀.underlying, _root_.Prime π →
        Int.ModEq (S.m : ℤ)
          (((emultiplicity π A).toNat : ℤ) - ((emultiplicity π B).toNat : ℤ))
          (∑ j, if Point.map p₀ (eY (y j)) = z₀
            then ((g32p_exponents S).get j : ℤ) else 0) := by
  letI : SmoothOfRelativeDimension 1 Y.hom := by
    simpa only [hdimY] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Y.left) Y.hom)
  letI : SmoothOfRelativeDimension 1 Z.hom := by
    simpa only [hdimZ] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Z.left) Z.hom)
  letI : Surjective p₀.left := ⟨s2_surjective_of_point_surjective p₀ hpsurj⟩
  letI : IsDominant p₀.left := inferInstance
  letI : Algebra ℂ Y.left.functionField := HodgeLean.Foundations.Curves.functionFieldAlgebra Y
  have hm : S.m ≠ 0 := by have := S.three_le; omega
  intro κZ τY u v hκ hτ hu hpow heigen z₀ A B hA hB hv π hπ
  have hκeq := s2v_l1b_divisor_generic_map p₀.left κZ hκ
  rw [hκeq] at hpow
  have hpresentation : u ^ S.m = s2v_l1b_functionFieldPullback p₀.left
      (algebraMap _ Z.left.functionField A / algebraMap _ Z.left.functionField B) := by
    rw [← hv]
    exact hpow
  by_cases hj : ∃ j, Point.map p₀ (eY (y j)) = z₀
  · obtain ⟨j, rfl⟩ := hj
    have hsum : (∑ i, if Point.map p₀ (eY (y i)) = Point.map p₀ (eY (y j))
        then ((g32p_exponents S).get i : ℤ) else 0) = ((g32p_exponents S).get j : ℤ) := by
      simp only [hy.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsum]
    obtain ⟨hp, ι, hι, hX, hc, hcomp⟩ := hcomparison j
    apply s2v_l1b_divisor_label_residue Y Z (S.H ⧸ S.χ.ker) hm a ha1 hamul e p₀ hp₀ hpsurj
      hporbit (rsq_Quot S.χ.ker C) eY hpointAction (y j) (rot j) (hrot j).1.1
      (hrot j).1.2.1 ((g32p_exponents S).get j) (hrot j).2 s hs hp ι hι hX hc hcomp
      τY hτ u hu ?_ A B hA hB hpresentation π hπ
    change τY u = Y.left.germToFunctionField ⊤
      (Y.hom.appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso ↧ℂ).inv.hom
        (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))))) * u
    simpa [CommRingCat.hom_comp, Scheme.Hom.appLE] using heigen
  · have hsum : (∑ j, if Point.map p₀ (eY (y j)) = z₀
        then ((g32p_exponents S).get j : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact if_neg (fun h => hj ⟨j, h⟩)
    rw [hsum]
    obtain ⟨x, rfl⟩ := hpsurj z₀
    have hstab : MulAction.stabilizer (S.H ⧸ S.χ.ker) (eY.symm x) = ⊥ := by
      by_contra hn
      obtain ⟨j, hj'⟩ := (hbranch (eY.symm x)).mp hn
      apply hj
      refine ⟨j, ?_⟩
      simpa only [eY.apply_symm_apply] using hj'.symm
    have hfree (g : S.H ⧸ S.χ.ker) : Point.map (a g) x = x ↔ g = 1 := by
      have hp := hpointAction g (eY.symm x)
      rw [eY.apply_symm_apply] at hp
      constructor
      · intro h
        have h' : g • eY.symm x = eY.symm x :=
          eY.injective ((hp.symm.trans h).trans (eY.apply_symm_apply x).symm)
        change g ∈ MulAction.stabilizer (S.H ⧸ S.χ.ker) (eY.symm x) at h'
        rw [hstab] at h'
        exact h'
      · rintro rfl
        rw [ha1, Point.map_id]
    exact s2v_l1b_divisor_unbranched_residue Y Z (S.H ⧸ S.χ.ker) hm a ha1 hamul p₀ hp₀
      hpsurj hporbit x hfree u hu A B hA hB hpresentation π hπ

theorem s2v_l1b_divisor_symmetric_quotient_aux
    (S : g32p_Supplier) (Y Z W₀ B₀ : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W₀.left] [IsProjective W₀.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom] [IsProjective B₀.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p₀ : Y ⟶ Z) [IsFinite p₀.left]
    (hp₀ : ∀ u, a u ≫ p₀ = p₀)
    (hpsurj : Function.Surjective (Point.map p₀))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (r : ℕ) (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length)
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker)
    (hrot : ∀ t, b4_IsRotGen ℂ (y t) (rot t) ∧
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S).get (t) : ZMod S.m))
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t))))
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t)))
    (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S).get (t) ∧ (g32p_exponents S).get (t) < S.m)
    (hpair : ∀ i : Fin r,
      (g32p_exponents S).get (σ ⟨2 * i.val, by omega⟩) +
      (g32p_exponents S).get (σ ⟨2 * i.val + 1, by omega⟩) = S.m)
    (h : ℕ) (hh : 0 < h + 1)
    (q₀ : g3_power Y (h + 1) ⟶ W₀) [IsFinite q₀.left]
    (hqsurj : Function.Surjective (Point.map q₀))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (β₀ : W₀ ⟶ B₀) [IsFinite β₀.left]
    (hβ₀ : q₀ ≫ β₀ = s2_powerMap p₀ (h + 1) ≫ γ)
    (d₀ : W₀ ⟶ W₀) (hd₀ : d₀ ≫ β₀ = β₀)
    (hgenerator : q₀ ≫ d₀ =
      s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q₀)
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hcomparison :
    ∀ j : Fin (g32p_exponents S).length,
      let p := (eY (y j)).left (IsLocalRing.closedPoint ℂ)
      ∃ (hp : (a (rot j)).left p = p)
        (ι : Y.left.presheaf.stalk p →+* PowerSeries ℂ),
        Function.Injective ι ∧
        (∃ u : Y.left.presheaf.stalk p, ι u = PowerSeries.X) ∧
        (∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC p c) = PowerSeries.C c) ∧
        ∀ v : Y.left.presheaf.stalk p,
          ι (s2e_fixed_point_stalkPullback Y.left (a (rot j)).left p hp v) =
            PowerSeries.rescale
              (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) /
                (orderOf (rot j) : ℂ))) (ι v))
    (t : W₀.left.functionField) (τ : W₀.left.functionField ≃+* W₀.left.functionField)
    (ht : t ≠ 0)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      W₀.left.fromSpecStalk (genericPoint W₀.left) =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ d₀.left)
    (hcharacter : τ t = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ W₀.hom.appTop ≫
      W₀.left.germToFunctionField ⊤).hom
      (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))) * t)
    (hcurve : ∀ (κZ : Z.left.functionField ⟶ Y.left.functionField)
      (τY : Y.left.functionField ≃+* Y.left.functionField)
      (u : Y.left.functionField) (v : Z.left.functionField),
      Spec.map κZ ≫ Z.left.fromSpecStalk (genericPoint Z.left) =
        Y.left.fromSpecStalk (genericPoint Y.left) ≫ p₀.left →
      Spec.map (CommRingCat.ofHom τY.toRingHom) ≫
          Y.left.fromSpecStalk (genericPoint Y.left) =
        Y.left.fromSpecStalk (genericPoint Y.left) ≫
          (a (e.symm (Multiplicative.ofAdd (1 : ZMod S.m)))).left →
      u ≠ 0 → u ^ S.m = κZ.hom v →
      τY u = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
        Y.left.germToFunctionField ⊤).hom
          (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))) * u →
      ∀ (z₀ : ComplexPoint Z) (A B : Z.left.presheaf.stalk z₀.underlying),
        A ≠ 0 → B ≠ 0 →
        v = algebraMap (Z.left.presheaf.stalk z₀.underlying) Z.left.functionField A /
          algebraMap (Z.left.presheaf.stalk z₀.underlying) Z.left.functionField B →
        ∀ π : Z.left.presheaf.stalk z₀.underlying, _root_.Prime π →
        Int.ModEq (S.m : ℤ)
          (((emultiplicity π A).toNat : ℤ) - ((emultiplicity π B).toNat : ℤ))
          (∑ j, if Point.map p₀ (eY (y j)) = z₀
            then ((g32p_exponents S).get j : ℤ) else 0)) :
    ∃ κ₀ : B₀.left.functionField ⟶ W₀.left.functionField,
      (Spec.map κ₀ ≫ B₀.left.fromSpecStalk (genericPoint B₀.left) =
        W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left) ∧
      ∀ x₀ : ComplexPoint B₀,
      ∃ (V₀ : B₀.left.affineOpens) (hx₀ : x₀.underlying ∈ V₀.1)
        (g₀ : Fin (2 * r) → Γ(B₀.left, V₀))
        (ε₀ : (B₀.left.presheaf.stalk x₀.underlying)ˣ)
        (A₀ B₁ : B₀.left.presheaf.stalk x₀.underlying),
        A₀ ≠ 0 ∧ B₁ ≠ 0 ∧
        (∀ j, (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ j))))).ideal V₀ =
          Ideal.span {g₀ j}) ∧
        let ρ₀ := s2v_l1b_kval_stalkMap B₀.left x₀.underlying κ₀
        t ^ S.m * (ρ₀ B₁) ^ S.m =
          ρ₀ (ε₀ : B₀.left.presheaf.stalk x₀.underlying) *
          (∏ j, ρ₀ ((B₀.left.presheaf.germ V₀.1 x₀.underlying hx₀).hom (g₀ j)) ^
            (g32p_exponents S).get (σ j)) * (ρ₀ A₀) ^ S.m := by
  obtain ⟨κ₀, hκinj, hκ₀, hκfin⟩ :=
    s2v_l1b_original_finite_field_embedding p₀ hpsurj (h + 1) q₀ γ
      hγsurj β₀ hβ₀
  refine ⟨κ₀, hκ₀, ?_⟩
  intro x₀
  obtain ⟨V₀, hx₀, hV₀, g₀, hg₀⟩ :=
    s2v_l1b_original_branches_simultaneous_equations Z B₀ B₀ hdimZ h γ
      hγsurj hγinv hγ (fun j : Fin (2 * r) => Point.map p₀ (eY (y (σ j))))
      (𝟙 B₀) x₀ ⊤ (by trivial)
  have hg₀' : ∀ j, (s2c_branchIdeal Z B₀ h γ
      (Point.map p₀ (eY (y (σ j))))).ideal V₀ = Ideal.span {g₀ j} := by
    simpa only [Over.id_left, Scheme.IdealSheafData.comap_id] using hg₀
  obtain ⟨hg_ne, A, B, hA, hB, hpow, horders⟩ :=
    s2v_l1b_divisor_quotient_prime_orders S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator s hs hcomparison t τ ht hτ hcharacter hcurve κ₀ hκ₀ x₀ V₀ hx₀ g₀ hg₀'
  letI := s2v_l1b_kval_stalk_factorial B₀ x₀.underlying
  let ρ := s2v_l1b_kval_stalkMap (K := W₀.left.functionField) B₀.left x₀.underlying κ₀
  have hρ : Function.Injective ρ := κ₀.hom.injective.comp
    (IsFractionRing.injective (B₀.left.presheaf.stalk x₀.underlying) B₀.left.functionField)
  obtain ⟨ε, A', B', hA', hB', heq⟩ := s2v_l1b_divisor_equation_of_orders ρ hρ
    (fun j => (B₀.left.presheaf.germ V₀.1 x₀.underlying hx₀).hom (g₀ j))
    (fun j => (g32p_exponents S).get (σ j)) hg_ne S.m
    (by have := S.three_le; omega) t A B hA hB hpow horders
  exact ⟨V₀, hx₀, g₀, ε, A', B', hA', hB', hg₀', heq⟩

set_option maxHeartbeats 400000 in
theorem s2v_l1b_divisor_tower_pullback_aux
    (S : g32p_Supplier) (Y Z W₀ B₀ : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W₀.left] [IsProjective W₀.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom] [IsProjective B₀.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p₀ : Y ⟶ Z) [IsFinite p₀.left]
    (hp₀ : ∀ u, a u ≫ p₀ = p₀)
    (hpsurj : Function.Surjective (Point.map p₀))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (r : ℕ) (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length)
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker)
    (hrot : ∀ t, b4_IsRotGen ℂ (y t) (rot t) ∧
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S).get (t) : ZMod S.m))
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t))))
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t)))
    (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S).get (t) ∧ (g32p_exponents S).get (t) < S.m)
    (hpair : ∀ i : Fin r,
      (g32p_exponents S).get (σ ⟨2 * i.val, by omega⟩) +
      (g32p_exponents S).get (σ ⟨2 * i.val + 1, by omega⟩) = S.m)
    (h : ℕ) (hh : 0 < h + 1)
    (q₀ : g3_power Y (h + 1) ⟶ W₀) [IsFinite q₀.left]
    (hqsurj : Function.Surjective (Point.map q₀))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (β₀ : W₀ ⟶ B₀) [IsFinite β₀.left]
    (hβ₀ : q₀ ≫ β₀ = s2_powerMap p₀ (h + 1) ≫ γ)
    (d₀ : W₀ ⟶ W₀) (hd₀ : d₀ ≫ β₀ = β₀)
    (hgenerator : q₀ ≫ d₀ =
      s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q₀)
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, Smooth (B i).hom]
    [∀ i, IsProjective (B i).hom]
    (e₀ : B 0 ≅ B₀) (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hD₀ : ∀ t, D 0 t =
      (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ t))))).comap e₀.hom.left)
    (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (hη₀ : η 0 ≫ e₀.hom.left = W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (heW : eW.hom ≫ β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom)
    (hgeneric : (η 0).toNormalization ≫ eW.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left))
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ s2b_normalizationOver (B i) (η i))
    (hd : ∀ i, d i ≫ s2b_normalizationMap (B i) (η i) = s2b_normalizationMap (B i) (η i))
    (hdinit : d 0 ≫ eW.hom = eW.hom ≫ d₀)
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (horder : ∀ i, (End.of (d i)) ^ S.m = 1)
    (i : Fin r)
    (x : ComplexPoint (B i.castSucc))
    (hx₁ : x.left (IsLocalRing.closedPoint ℂ) ∈
      (D i.castSucc ⟨2 * i.val, by omega⟩).support)
    (hx₂ : x.left (IsLocalRing.closedPoint ℂ) ∈
      (D i.castSucc ⟨2 * i.val + 1, by omega⟩).support)
    (havoid : ∀ t : Fin (2 * r), t.val ≠ 2 * i.val → t.val ≠ 2 * i.val + 1 →
      x.left (IsLocalRing.closedPoint ℂ) ∉ (D i.castSucc t).support)
    (κ : (B i.castSucc).left.functionField ⟶ W₀.left.functionField)
    (hκ : Spec.map κ ≫ (B i.castSucc).left.fromSpecStalk
        (genericPoint (B i.castSucc).left) = η i.castSucc)
    (hfield : letI := κ.hom.toAlgebra
       Module.Finite (B i.castSucc).left.functionField W₀.left.functionField ∧
       IsGalois (B i.castSucc).left.functionField W₀.left.functionField ∧
       IsCyclic (W₀.left.functionField ≃ₐ[(B i.castSucc).left.functionField]
         W₀.left.functionField) ∧
       Module.finrank (B i.castSucc).left.functionField W₀.left.functionField = S.m)
    (R : Type) [CommRing R]
    (eR : R ≃+* (B i.castSucc).left.presheaf.stalk (x.left (IsLocalRing.closedPoint ℂ)))
    [IsDomain R] [UniqueFactorizationMonoid R]
    (V : (B i.castSucc).left.affineOpens)
    (hxV : x.left (IsLocalRing.closedPoint ℂ) ∈ V.1)
    (cV : ∀ j : Fin (i.val + 1), B i.castSucc ⟶ B ⟨j.val, by omega⟩)
    (gV : Fin (2 * r) → Γ((B i.castSucc).left, V))
    (hcV : cV (Fin.last i.val) = 𝟙 (B i.castSucc))
    (hbV : ∀ j : Fin i.val, cV j.succ ≫ b ⟨j.val, by omega⟩ = cV j.castSucc)
    (hgV : ∀ j, ((s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ j))))).comap
      (cV 0 ≫ e₀.hom).left).ideal V = Ideal.span {gV j})
    (hfne : ∀ j, eR.symm (((B i.castSucc).left.presheaf.germ V.1
      (x.left (IsLocalRing.closedPoint ℂ)) hxV).hom (gV j)) ≠ 0)
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hcomparison :
    ∀ j : Fin (g32p_exponents S).length,
      let p := (eY (y j)).left (IsLocalRing.closedPoint ℂ)
      ∃ (hp : (a (rot j)).left p = p)
        (ι : Y.left.presheaf.stalk p →+* PowerSeries ℂ),
        Function.Injective ι ∧
        (∃ u : Y.left.presheaf.stalk p, ι u = PowerSeries.X) ∧
        (∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC p c) = PowerSeries.C c) ∧
        ∀ v : Y.left.presheaf.stalk p,
          ι (s2e_fixed_point_stalkPullback Y.left (a (rot j)).left p hp v) =
            PowerSeries.rescale
              (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) /
                (orderOf (rot j) : ℂ))) (ι v))
    (U : (B i.castSucc).left.affineOpens) (hn : 2 ≤ h + 1)
    (z : Fin (h + 1) → Γ((B i.castSucc).left, U))
    (hxU : x.left (IsLocalRing.closedPoint ℂ) ∈ U.1)
    (hEt : (MvPolynomial.eval₂Hom ((B i.castSucc).hom.appLE ⊤ U.1 le_top).hom z).Etale)
    (hz₀ : (D i.castSucc ⟨2 * i.val, by omega⟩).ideal U =
      Ideal.span {z ⟨0, by omega⟩})
    (hz₁ : (D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U =
      Ideal.span {z ⟨1, by omega⟩})
    (t : W₀.left.functionField) (a₁ b₁ : R)
    (τ : W₀.left.functionField ≃+* W₀.left.functionField)
    (ha₁ : a₁ ≠ 0) (hb₁ : b₁ ≠ 0) (ht : t ≠ 0)
    (hgen : let ρ := (s2v_l1b_kval_stalkMap (K := W₀.left.functionField) (B i.castSucc).left
      (x.left (IsLocalRing.closedPoint ℂ)) κ).comp eR.toRingHom
      Subfield.closure (Set.range ρ ∪ {t}) = ⊤)
    (hpow : let ρ := (s2v_l1b_kval_stalkMap (K := W₀.left.functionField) (B i.castSucc).left
      (x.left (IsLocalRing.closedPoint ℂ)) κ).comp eR.toRingHom
      t ^ S.m = ρ a₁ / ρ b₁)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      W₀.left.fromSpecStalk (genericPoint W₀.left) =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ d₀.left)
    (hτorder : orderOf τ = S.m)
    (hfix : let ρ := (s2v_l1b_kval_stalkMap (K := W₀.left.functionField) (B i.castSucc).left
      (x.left (IsLocalRing.closedPoint ℂ)) κ).comp eR.toRingHom
      ∀ v : R, τ (ρ v) = ρ v)
    (hcharacter : τ t = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ W₀.hom.appTop ≫ W₀.left.germToFunctionField ⊤).hom (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))) * t)
    (p : R) (hp : _root_.Prime (M := R) p)
    (κ₀ : B₀.left.functionField ⟶ W₀.left.functionField)
    (hκ₀ : Spec.map κ₀ ≫ B₀.left.fromSpecStalk (genericPoint B₀.left) =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left)
    (hquotient : ∀ x₀ : ComplexPoint B₀,
      ∃ (V₀ : B₀.left.affineOpens) (hx₀ : x₀.underlying ∈ V₀.1)
        (g₀ : Fin (2 * r) → Γ(B₀.left, V₀))
        (ε₀ : (B₀.left.presheaf.stalk x₀.underlying)ˣ)
        (A₀ B₁ : B₀.left.presheaf.stalk x₀.underlying),
        A₀ ≠ 0 ∧ B₁ ≠ 0 ∧
        (∀ j, (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ j))))).ideal V₀ =
          Ideal.span {g₀ j}) ∧
        let ρ₀ := s2v_l1b_kval_stalkMap B₀.left x₀.underlying κ₀
        t ^ S.m * (ρ₀ B₁) ^ S.m =
          ρ₀ (ε₀ : B₀.left.presheaf.stalk x₀.underlying) *
          (∏ j, ρ₀ ((B₀.left.presheaf.germ V₀.1 x₀.underlying hx₀).hom (g₀ j)) ^
            (g32p_exponents S).get (σ j)) * (ρ₀ A₀) ^ S.m) :
    let f := fun j => eR.symm (((B i.castSucc).left.presheaf.germ V.1
      (x.left (IsLocalRing.closedPoint ℂ)) hxV).hom (gV j))
    Int.ModEq (S.m : ℤ)
      (((emultiplicity (α := R) p a₁).toNat : ℤ) -
        ((emultiplicity (α := R) p b₁).toNat : ℤ))
      (∑ j : Fin (2 * r), ((g32p_exponents S).get (σ j) : ℤ) *
        ((emultiplicity (α := R) p (f j)).toNat : ℤ)) := by
  let f := cV 0 ≫ e₀.hom
  have hc : η i.castSucc ≫ (cV 0).left = η 0 :=
    s2v_l1b_earlier_maps_generic
      (fun j : Fin (i.val + 1) => (B ⟨j.val, by omega⟩).left)
      (fun j => (b ⟨j.val, by omega⟩).left) (fun j => (cV j).left)
      (congrArg Over.Hom.left hcV) (fun j => congrArg Over.Hom.left (hbV j))
      _ (fun j => η ⟨j.val, by omega⟩) (fun j => hη ⟨j.val, by omega⟩) 0
  have hsq : Spec.map κ ≫ (B i.castSucc).left.fromSpecStalk
      (genericPoint (B i.castSucc).left) ≫ f.left =
      Spec.map κ₀ ≫ B₀.left.fromSpecStalk (genericPoint B₀.left) := by
    change Spec.map κ ≫ (B i.castSucc).left.fromSpecStalk _ ≫
      (cV 0).left ≫ e₀.hom.left = _
    rw [← Category.assoc, hκ, ← Category.assoc, hc, hη₀, hκ₀]
  have hqpoint := hquotient (Point.map f x)
  have hxpoint : x.underlying = x.left (IsLocalRing.closedPoint ℂ) := rfl
  rw [Point.underlying_map, hxpoint] at hqpoint
  obtain ⟨V₀, hx₀, g₀, ε₀, A₀, B₁, hA, hB, hg₀, he⟩ := hqpoint
  have H := s2v_l1b_divisor_pullback_residue (K := W₀.left.functionField)
    (R := R) (J := Fin (2 * r)) (X := (B i.castSucc).left) (Y := B₀.left)
    f.left κ κ₀ hsq (x.left (IsLocalRing.closedPoint ℂ)) eR
    (fun j => s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ j)))))
  have H1 := H V hxV gV hgV
  have H2 := H1 V₀ hx₀ g₀ hg₀ ε₀ A₀ B₁ hA hB
  have H3 := H2 (fun j => (g32p_exponents S).get (σ j)) S.m t a₁ b₁ ha₁ hb₁ hfne hpow he p hp
  exact H3

end HodgeLean.Foundations.Program

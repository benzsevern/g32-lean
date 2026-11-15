import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorSymmetricOrders
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductReference
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorResidualQuotient
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorQuotientRatio
import HodgeLean.Foundations.Program.SchoenTowerL1bKvalFactorial
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorOriginalGenerator
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorBranchNonzero
import HodgeLean.Foundations.Program.SchoenTowerL1bBranchEquations
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerInitial
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



theorem s2v_l1b_divisor_quotient_incidence_orders
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
            then ((g32p_exponents S).get j : ℤ) else 0))
    (κ₀ : B₀.left.functionField ⟶ W₀.left.functionField)
    (hκ₀ : Spec.map κ₀ ≫ B₀.left.fromSpecStalk (genericPoint B₀.left) =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left)
    (x₀ : ComplexPoint B₀) (V₀ : B₀.left.affineOpens)
    (hx₀ : x₀.underlying ∈ V₀.1) (g₀ : Fin (2 * r) → Γ(B₀.left, V₀))
    (hg₀ : ∀ j, (s2c_branchIdeal Z B₀ h γ
      (Point.map p₀ (eY (y (σ j))))).ideal V₀ = Ideal.span {g₀ j})
    (A B : B₀.left.presheaf.stalk x₀.underlying) (hA : A ≠ 0) (hB : B ≠ 0)
    (hpow : t ^ S.m =
      s2v_l1b_kval_stalkMap (K := W₀.left.functionField) B₀.left x₀.underlying κ₀ A /
      s2v_l1b_kval_stalkMap (K := W₀.left.functionField) B₀.left x₀.underlying κ₀ B) :
    let g := fun j => (B₀.left.presheaf.germ V₀.1 x₀.underlying hx₀).hom (g₀ j)
    (∀ j, g j ≠ 0) ∧
    ∀ p : B₀.left.presheaf.stalk x₀.underlying, Prime p →
      Int.ModEq (S.m : ℤ)
        (((emultiplicity p A).toNat : ℤ) - ((emultiplicity p B).toNat : ℤ))
        (∑ j, ((g32p_exponents S).get (σ j) : ℤ) *
          ((emultiplicity p (g j)).toNat : ℤ)) := by
  refine ⟨?_, ?_⟩
  · intro j
    exact s2v_l1b_divisor_branch_germ_ne_zero Z B₀ hdimZ h γ hγsurj hγinv hγ
      (Point.map p₀ (eY (y (σ j)))) x₀ V₀ hx₀ (g₀ j) (hg₀ j)
  · obtain ⟨κZ, τY, u, v, hκZ, hτY, hu, huv, huchar⟩ :=
      s2v_l1b_divisor_original_generator S Y Z a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit s hs
    have hcurveOrders := hcurve κZ τY u v hκZ hτY hu huv huchar
    letI : IsDominant q₀.left := n1bc_dominant_of_points_surjective q₀ hqsurj
    letI : IsDominant γ.left := n1bc_dominant_of_points_surjective γ hγsurj
    letI : IsDominant β₀.left := n1bc_dominant_of_points_surjective β₀
      (n1bc_originalCover_points_surjective p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀)
    obtain ⟨w, b, hw, hb, hqw, hγb, hwb, hwchar⟩ :=
      s2v_l1b_divisor_product_reference S Y Z W₀ B₀ a e ha1 hamul p₀ hpsurj
        (h + 1) hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hgenerator
        s hs κZ hκZ τY hτY u v hu huv huchar τ hτ
    obtain ⟨C₀, D₀, hD, hCD⟩ := IsFractionRing.div_surjective
      (B₀.left.presheaf.stalk x₀.underlying) b
    have hD₀ : D₀ ≠ 0 := nonZeroDivisors.ne_zero hD
    have hC₀ : C₀ ≠ 0 := by
      intro hz
      rw [hz, map_zero, zero_div] at hCD
      exact hb hCD.symm
    have hwm : w ^ S.m =
        s2v_l1b_kval_stalkMap B₀.left x₀.underlying (s2v_l1b_functionFieldPullback β₀.left) C₀ /
        s2v_l1b_kval_stalkMap B₀.left x₀.underlying (s2v_l1b_functionFieldPullback β₀.left) D₀ := by
      rw [hwb, s2v_l1b_kval_stalkMap, RingHom.comp_apply, RingHom.comp_apply,
        ← map_div₀, hCD]
    have hκeq := s2v_l1b_divisor_generic_map β₀.left κ₀ hκ₀
    have htm := hpow
    rw [hκeq] at htm
    obtain ⟨hdiso, hcat⟩ := s2v_l1b_divisor_residual_quotient S Y Z W₀ B₀ a e
      ha1 hamul hinj p₀ hp₀ hpsurj hporbit (h + 1) hh q₀ hqinv hq γ hγsurj hγinv hγ
      β₀ hβ₀ d₀ hgenerator
    letI : IsIso d₀ := hdiso
    letI := s2v_l1b_kval_stalk_factorial B₀ x₀.underlying
    let ζ := Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))
    let cW : CommRingCat.of ℂ ⟶ W₀.left.functionField :=
      (Scheme.ΓSpecIso ↧ℂ).inv ≫ W₀.hom.appTop ≫ W₀.left.germToFunctionField ⊤
    have hξ : cW.hom ζ ≠ 0 := by
      simpa only [map_zero] using cW.hom.injective.ne (Complex.exp_ne_zero _)
    have hv : v ≠ 0 := by
      intro hz
      rw [hz, map_zero] at huv
      exact pow_ne_zero S.m hu huv
    have hgeo := s2v_l1b_divisor_symmetric_product_orders Z B₀ hdimZ h γ hγsurj hγinv hγ
      (fun j : Fin (2 * r) => Point.map p₀ (eY (y (σ j)))) (hy.comp σ.injective)
      (fun j => (g32p_exponents S).get (σ j)) S.m v hv
      (by
        intro z C D hC hD hvCD π hπ
        have H := hcurveOrders z C D hC hD hvCD π hπ
        rw [← Equiv.sum_comp σ (fun j => if Point.map p₀ (eY (y j)) = z
          then ((g32p_exponents S).get j : ℤ) else 0)] at H
        exact H)
      b hγb x₀ V₀ hx₀ g₀ hg₀ C₀ D₀ hC₀ hD₀ hCD.symm
    intro p hp
    have hres := s2v_l1b_divisor_quotient_character_residue W₀ B₀ β₀ d₀ hd₀ hcat τ hτ
      t w (cW.hom ζ) ht hw hξ hcharacter hwchar x₀.underlying
      A B C₀ D₀ hA hB hC₀ hD₀ S.m htm hwm p hp
    exact hres.trans (hgeo p hp)

end HodgeLean.Foundations.Program

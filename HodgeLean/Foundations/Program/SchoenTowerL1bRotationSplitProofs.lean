import HodgeLean.Foundations.Program.SchoenTowerL1bActionSplit
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportSplit
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

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- One orientation sign identifies the actual fixed-point stalk actions with
formal rotations at every listed branch point.
Source: Schoen (1988), Lemma 2.5, printed p. 15; Miranda, Algebraic Curves and
Riemann Surfaces, III.3, Proposition 3.1, local cyclic actions. -/
theorem s2v_l1b_rotation_action_comparison_aux
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
 :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
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
                (orderOf (rot j) : ℂ))) (ι v) := by
  classical
  let hp (j : Fin (g32p_exponents S).length) :=
    s2v_l1b_rotation_scheme_fixed Y a eY hpointAction (rot j) (y j) (hrot j).1.1
  have hdata (j : Fin (g32p_exponents S).length) :=
    s2v_l1b_rotation_curve_action_expansion Y hdimY a ha1 hamul (rot j)
      (eY (y j)) (hp j) (orderOf (rot j)) (orderOf_pos (rot j))
      (pow_orderOf_eq_one (rot j))
  choose ζ hζ ι hι hX hC hact using hdata
  have hsign (j : Fin (g32p_exponents S).length) :=
    s2v_l1b_action_label_sign S Y hdimY a ha1 hamul C eY hpointAction
      (y j) (rot j) (hrot j).1 (hp j) (ζ j) (hζ j) (ι j) (hι j)
      (hX j) (hC j) (hact j)
  choose ε hε horient hscalar using hsign
  obtain ⟨s, hs, heps⟩ := s2v_l1b_action_orientation_constant Y hdimY
    (rsq_Quot S.χ.ker C) eY (Fin (g32p_exponents S).length) y ε hε horient
  refine ⟨s, hs, ?_⟩
  intro j
  refine ⟨hp j, ι j, hι j, hX j, hC j, ?_⟩
  intro v
  have hv := hact j v
  rw [hscalar j, heps j] at hv
  exact hv

/-- Character transport supplies a generating binomial and formal local fractions
whose ramification equations identify all prime orders with the total branch germs.
Source: Schoen (1988), Lemmas 2.2 and 2.5, printed pp. 13 and 15. -/
theorem s2v_l1b_rotation_character_transport_aux
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
      Ideal.span {z ⟨1, by omega⟩}) :
    let ρ := (s2v_l1b_kval_stalkMap (K := W₀.left.functionField) (B i.castSucc).left
      (x.left (IsLocalRing.closedPoint ℂ)) κ).comp eR.toRingHom
    let f := fun j => eR.symm (((B i.castSucc).left.presheaf.germ V.1
      (x.left (IsLocalRing.closedPoint ℂ)) hxV).hom (gV j))
    ∃ (t : W₀.left.functionField) (a₁ b₁ : R),
      a₁ ≠ 0 ∧ b₁ ≠ 0 ∧ t ≠ 0 ∧
      Subfield.closure (Set.range ρ ∪ {t}) = ⊤ ∧
      t ^ S.m = ρ a₁ / ρ b₁ ∧
      ∃ τ : W₀.left.functionField ≃+* W₀.left.functionField,
        Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
            W₀.left.fromSpecStalk (genericPoint W₀.left) =
          W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ d₀.left ∧
      ∀ p : R, _root_.Prime (M := R) p →
        ∃ (K : Type) (hK : Field K),
          letI := hK
          ∃ (L : Type) (hL : Field L),
          letI := hL
          ∃ (ψ : W₀.left.functionField →+* L) (ι : PowerSeries K →+* L)
            (e k : ℕ) (q l : ℤ) (ζ : K) (F G : PowerSeries K),
          Function.Injective ψ ∧ Function.Injective ι ∧
          ψ t = ι F / ι G ∧
          e ≠ 0 ∧ IsPrimitiveRoot ζ e ∧ F ≠ 0 ∧ G ≠ 0 ∧
          (S.m : ℤ) = (e : ℤ) * q ∧
          ψ ((τ ^ q.toNat) t) = ι (PowerSeries.C (ζ ^ k)) * ψ t ∧
          PowerSeries.rescale ζ F * G =
            PowerSeries.C (ζ ^ k) * (F * PowerSeries.rescale ζ G) ∧
          (S.m : ℤ) * ((F.order.toNat : ℤ) - (G.order.toNat : ℤ)) =
            (e : ℤ) * (((emultiplicity (α := R) p a₁).toNat : ℤ) -
              ((emultiplicity (α := R) p b₁).toNat : ℤ)) ∧
          q * (k : ℤ) =
            (∑ j : Fin (2 * r), ((g32p_exponents S).get (σ j) : ℤ) *
              ((emultiplicity (α := R) p (f j)).toNat : ℤ)) + (S.m : ℤ) * l := by
  obtain ⟨t, a₁, b₁, ha₁, hb₁, ht, hgen, hpow, τ, hτ, hτorder, hfix, hcharacter⟩ :=
    s2v_l1b_transport_actual_character S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid κ hκ hfield R eR V hxV cV gV hcV hbV hgV hfne s hs hcomparison U hn z hxU hEt hz₀ hz₁
  have hlocal := s2v_l1b_transport_local_expansions S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid κ hκ hfield R eR V hxV cV gV hcV hbV hgV hfne s hs hcomparison U hn z hxU hEt hz₀ hz₁ t a₁ b₁ τ ha₁ hb₁ ht hgen hpow hτ hτorder hfix hcharacter
  refine ⟨t, a₁, b₁, ha₁, hb₁, ht, hgen, hpow, τ, hτ, ?_⟩
  intro p hp
  obtain ⟨K, hK, hdata⟩ := hlocal p hp
  letI := hK
  obtain ⟨L, hL, hdata⟩ := hdata
  letI := hL
  obtain ⟨ψ, ι, ee, k, q, ζ, F, G, hψ, hι, hfrac, he, hζ, hF, hG,
    hm, heigen, hcross, hram⟩ := hdata
  obtain ⟨l, hweight⟩ := s2v_l1b_transport_generator_orders S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid κ hκ hfield R eR V hxV cV gV hcV hbV hgV hfne s hs hcomparison U hn z hxU hEt hz₀ hz₁ t a₁ b₁ τ ha₁ hb₁ ht hgen hpow hτ hτorder hfix hcharacter p hp K L ψ ι ee k q ζ F G hψ hι hfrac he hζ hF hG hm heigen hcross hram
  exact ⟨K, hK, L, hL, ψ, ι, ee, k, q, l, ζ, F, G, hψ, hι, hfrac,
    he, hζ, hF, hG, hm, heigen, hcross, hram, hweight⟩

end HodgeLean.Foundations.Program

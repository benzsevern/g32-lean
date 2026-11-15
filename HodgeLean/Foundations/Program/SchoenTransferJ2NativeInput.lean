import HodgeLean.Foundations.WitnessSelection.StageTwo.Defs
import HodgeLean.Foundations.Program.SchoenTransferQ2cApplications
/-! # S4 selected witness applications

Implications from the literal retained S2 alternatives and realization choices.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 4000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Papers
open scoped BigOperators Manifold ContDiff OnePoint TensorProduct
namespace HodgeLean.Foundations.Program
variable (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J))

/-- Identity on the literal uniform native supplier input, for sharing its elaborated type.
Source: s4-chain-contract.md, J1/J2 input telescope, rows 307–351.
HC no distance; AV milestone no distance. -/
theorem s4_chain_native_input_identity (hNative :
    (∀ (S : g32p_Supplier), g32p_Admissible aut S →
(∃ (Y Z W₀ B₀ : Over (Spec ↧ℂ)),
∃ inst1 : IsIntegral Y.left,
    let := inst1
∃ inst2 : Smooth Y.hom,
    let := inst2
∃ inst3 : IsProjective Y.hom,
    let := inst3
∃ inst4 : IsIntegral Z.left,
    let := inst4
∃ inst5 : Smooth Z.hom,
    let := inst5
∃ inst6 : IsProjective Z.hom,
    let := inst6
∃ inst7 : IsIntegral W₀.left,
    let := inst7
∃ inst8 : IsProjective W₀.hom,
    let := inst8
∃ inst9 : IsIntegral B₀.left,
    let := inst9
∃ inst10 : Smooth B₀.hom,
    let := inst10
∃ inst11 : IsProjective B₀.hom,
    let := inst11
∃ (hdimY : TopologicalSpace.dim Y.left = 1),
∃ (hdimZ : TopologicalSpace.dim Z.left = 1),
∃ (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y)),
∃ (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m)),
∃ (ha1 : a 1 = 𝟙 Y),
∃ (hamul : ∀ u v, a (u * v) = a v ≫ a u),
∃ (hinj : Function.Injective a),
∃ (p₀ : Y ⟶ Z),
∃ inst12 : IsFinite p₀.left,
    let := inst12
∃ (hp₀ : ∀ u, a u ≫ p₀ = p₀),
∃ (hpsurj : Function.Surjective (Point.map p₀)),
∃ (hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y),
∃ (C : Type),
∃ inst13 : TopologicalSpace C,
    let := inst13
∃ inst14 : MulAction g32p_G C,
    let := inst14
∃ inst15 : ChartedSpace ℂ (rsq_Quot S.χ.ker C),
    let := inst15
∃ inst16 : IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C),
    let := inst16
∃ (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y),
∃ (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y)),
∃ (r : ℕ),
∃ (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length),
∃ (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C),
∃ (rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker),
∃ (hrot : ∀ t, b4_IsRotGen ℂ (y t) (rot t) ∧
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S)[t] : ZMod S.m)),
∃ (hy : Function.Injective (fun t => Point.map p₀ (eY (y t)))),
∃ (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t))),
∃ (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S)[t] ∧ (g32p_exponents S)[t] < S.m),
∃ (hpair : ∀ i : Fin r,
      (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩] +
      (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] = S.m),
∃ (h : ℕ),
∃ (hh : 0 < h + 1),
∃ (q₀ : g3_power Y (h + 1) ⟶ W₀),
∃ inst17 : IsFinite q₀.left,
    let := inst17
∃ (hqsurj : Function.Surjective (Point.map q₀)),
∃ (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀),
∃ (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f),
∃ (γ : g3_power Z (h + 1) ⟶ B₀),
∃ inst18 : IsFinite γ.left,
    let := inst18
∃ (hγsurj : Function.Surjective (Point.map γ)),
∃ (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ),
∃ (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f),
∃ (β₀ : W₀ ⟶ B₀),
∃ inst19 : IsFinite β₀.left,
    let := inst19
∃ (hβ₀ : q₀ ≫ β₀ = s2_powerMap p₀ (h + 1) ≫ γ),
∃ (d₀ : W₀ ⟶ W₀),
∃ (hd₀ : d₀ ≫ β₀ = β₀),
∃ (hgenerator : q₀ ≫ d₀ =
      s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q₀),
∃ (B : Fin (r + 1) → Over (Spec ↧ℂ)),
∃ inst20 : ∀ i, IsIntegral (B i).left,
    let := inst20
∃ inst21 : ∀ i, Smooth (B i).hom,
    let := inst21
∃ inst22 : ∀ i, IsProjective (B i).hom,
    let := inst22
∃ (e₀ : B 0 ≅ B₀),
∃ (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc),
∃ (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData),
∃ (hD₀ : ∀ t, D 0 t =
      (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ t))))).comap e₀.hom.left),
∃ (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩)),
∃ (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U))),
∃ (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f),
∃ (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left),
∃ inst23 : ∀ i, QuasiCompact (η i),
    let := inst23
∃ inst24 : ∀ i, QuasiSeparated (η i),
    let := inst24
∃ (hη₀ : η 0 ≫ e₀.hom.left = W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left),
∃ (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc),
∃ (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀),
∃ (heW : eW.hom ≫ β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom),
∃ (hgeneric : (η 0).toNormalization ≫ eW.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left)),
∃ (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc)),
∃ (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization),
∃ (d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ s2b_normalizationOver (B i) (η i)),
∃ (hd : ∀ i, d i ≫ s2b_normalizationMap (B i) (η i) = s2b_normalizationMap (B i) (η i)),
∃ (hdinit : d 0 ≫ eW.hom = eW.hom ≫ d₀),
∃ (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc),
∃ (horder : ∀ i, (End.of (d i)) ^ S.m = 1),
∃ (C₀ : Over (Spec ↧ℂ)),
∃ inst25 : IsIntegral C₀.left,
    let := inst25
∃ inst26 : Smooth C₀.hom,
    let := inst26
∃ inst27 : IsProjective C₀.hom,
    let := inst27
∃ (P : g32p_Part J aut S),
∃ (qC : C₀ ⟶ Y),
∃ (jC : C₀ ⟶ J),
∃ (eC : C ≃ₜ ComplexPoint C₀),
∃ (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z),
∃ (hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x)),
∃ (hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z)),
∃ (hχ : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u),
∃ (hjC : Function.Bijective (homPullback jC 1)),
∃ (primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))),
∃ (hprimitive : ∀ v, homPullback qC 1 (primitive v) =
      homPullback jC 1 (homPullback P.proj 1 v)),
∃ (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1)),
∃ (hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m),
∃ (hselected : h + 1 = 2 * P.k),
∃ inst28 : ChartedSpace ℂ (rsq_Quot S.H C),
    let := inst28
∃ inst29 : IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C),
    let := inst29
∃ (hgenus : 2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
      (g32p_exponents S).length),
∃ (hExceptionalPrimitive : ∀ i : Fin r,
    let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let K := s2c_subscheme (B i.castSucc) I
    let kι := s2c_subschemeι (B i.castSucc) I
    let E := s2c_exceptional (b i) I
    let j : E ⟶ B i.succ := pullback.fst (b i) kι
    let p : E ⟶ K := pullback.snd (b i) kι
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    ∀ (n : ℕ) (ζ : ℂ), IsPrimitiveRoot ζ S.m →
      ∀ v : AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint (s2b_preimage β j))) n,
        s2b_preimageCohomologyDeck β j (d i.succ) (hd i.succ) n v = ζ • v → v = 0),
∃ (W : Over (Spec ↧ℂ)),
∃ (eWr : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W),
    let Xr := TopCat.of (ComplexPoint W)
    let X₀ := TopCat.of (ComplexPoint W₀)
    let H₀ := AlgebraicTopology.Singular.Cohomology ℚ X₀ (2 * P.k)
    let Hr := AlgebraicTopology.Singular.Cohomology ℚ Xr (2 * P.k)
    let δ := eWr.inv ≫ d (Fin.last r) ≫ eWr.hom
    ∃ f : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ W₀,
      f 0 = eW.hom ∧ (∀ i : Fin r, f i.succ = w i ≫ f i.castSucc) ∧
    let φ := eWr.inv ≫ f (Fin.last r)
    ∃ (hft : LocallyOfFiniteType W.hom) (hqc : QuasiCompact W.hom)
      (hsep : IsSeparated W.hom) (hφ : QuasiCompact φ.left),
    let := hft
    let := hqc
    let := hsep
    let := hφ
    ∃ (trr : AlgebraicTopology.Singular.Cohomology ℚ Xr (2 * (2 * P.k)) →ₗ[ℚ] ℚ)
      (tr₀ : AlgebraicTopology.Singular.Cohomology ℚ X₀ (2 * (2 * P.k)) →ₗ[ℚ] ℚ),
      Function.Bijective (s2e_middlePairing Xr P.k trr) ∧
      Function.Bijective (s2e_middlePairing X₀ P.k tr₀) ∧
      (∃ (U : W.left.Opens) (x : ComplexPoint W),
        Point.underlying x ∈ U ∧ Smooth (U.ι ≫ W.hom) ∧
        ∃ c, a3b4_IsCycleClass W.hom (s2e_componentCycle x ℚ) (2 * P.k) c ∧
          trr (s2e_classToAbsolute W (s2e_componentCycle x ℚ) (2 * P.k) c) = 1) ∧
      (∃ (U : W₀.left.Opens) (x : ComplexPoint W₀),
        Point.underlying x ∈ U ∧ Smooth (U.ι ≫ W₀.hom) ∧
        ∃ c, a3b4_IsCycleClass W₀.hom (s2e_componentCycle x ℚ) (2 * P.k) c ∧
          tr₀ (s2e_classToAbsolute W₀ (s2e_componentCycle x ℚ) (2 * P.k) c) = 1) ∧
    ∃ G : Hr →ₗ[ℚ] H₀,
      (∀ u v, s2e_middlePairing X₀ P.k tr₀ (G u) v =
        s2e_middlePairing Xr P.k trr u (s2e_pullback ℚ φ (2 * P.k) v)) ∧
      (∀ v, G (s2e_pullback ℚ φ (2 * P.k) v) = v) ∧
      (∀ v, G (s2e_pullback ℚ δ (2 * P.k) v) = s2e_pullback ℚ d₀ (2 * P.k) (G v)) ∧
    ∃ (Q : Over (Spec ↧ℂ)) (hQ : IsIntegral Q.left),
    let := hQ
    ∃ (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)))
      (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)) ⟶ B (Fin.last r))
      (ι : Q ⟶ W),
      IsClosedImmersion ℓ.left ∧ IsClosedImmersion ι.left ∧
      ι ≫ eWr.inv ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r)) = eQ.hom ≫ ℓ ∧
      (∀ t, Disjoint (Set.range ℓ.left) (D (Fin.last r) t).support) ∧
    ∃ (a : Fin (Nat.totient S.m) → Fin S.m → ℚ)
      (v : Fin (Nat.totient S.m) → H₀),
      LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = LinearMap.ker
        (Polynomial.aeval (s2e_pullback ℚ d₀ (2 * P.k)) (Polynomial.cyclotomic S.m ℚ)) ∧
      (∀ j,
        let γ := s2e_rationalOrbitCycle ι δ S.m (a j)
        (∀ x ∈ γ.support, Order.coheight x = P.k) ∧
        (∀ x ∈ (a1p_pushforward φ.left γ).support, Order.coheight x = P.k) ∧
        ∃ cr, a3b4_IsCycleClass W.hom γ P.k cr ∧
        ∃ c₀, a3b4_IsCycleClass W₀.hom (a1p_pushforward φ.left γ) P.k c₀ ∧
          G (s2e_classToAbsolute W γ P.k cr) = v j ∧
          s2e_classToAbsolute W₀ (a1p_pushforward φ.left γ) P.k c₀ = v j) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
        (∃ u : ℂ ⊗[ℚ] H₀, u ≠ 0 ∧
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u) ∧
        (∀ u : ℂ ⊗[ℚ] H₀,
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u →
          ∃ b : Fin (Nat.totient S.m) → ℂ,
            u = ∑ j, b j • TensorProduct.tmul ℚ (1 : ℂ) (v j))) ∨
(∃ (Y Z W₀ B₀ : Over (Spec ↧ℂ)),
∃ inst1 : IsIntegral Y.left,
    let := inst1
∃ inst2 : Smooth Y.hom,
    let := inst2
∃ inst3 : IsProjective Y.hom,
    let := inst3
∃ inst4 : IsIntegral Z.left,
    let := inst4
∃ inst5 : Smooth Z.hom,
    let := inst5
∃ inst6 : IsProjective Z.hom,
    let := inst6
∃ inst7 : IsIntegral W₀.left,
    let := inst7
∃ inst8 : IsProjective W₀.hom,
    let := inst8
∃ inst9 : IsIntegral B₀.left,
    let := inst9
∃ inst10 : Smooth B₀.hom,
    let := inst10
∃ inst11 : IsProjective B₀.hom,
    let := inst11
∃ (hdimY : TopologicalSpace.dim Y.left = 1),
∃ (hdimZ : TopologicalSpace.dim Z.left = 1),
∃ (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y)),
∃ (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m)),
∃ (ha1 : a 1 = 𝟙 Y),
∃ (hamul : ∀ u v, a (u * v) = a v ≫ a u),
∃ (hinj : Function.Injective a),
∃ (p₀ : Y ⟶ Z),
∃ inst12 : IsFinite p₀.left,
    let := inst12
∃ (hp₀ : ∀ u, a u ≫ p₀ = p₀),
∃ (hpsurj : Function.Surjective (Point.map p₀)),
∃ (hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y),
∃ (C : Type),
∃ inst13 : TopologicalSpace C,
    let := inst13
∃ inst14 : MulAction g32p_G C,
    let := inst14
∃ inst15 : ChartedSpace ℂ (rsq_Quot S.χ.ker C),
    let := inst15
∃ inst16 : IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C),
    let := inst16
∃ (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y),
∃ (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y)),
∃ (r : ℕ),
∃ (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length),
∃ (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C),
∃ (rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker),
∃ (hrot : ∀ t, b4_IsRotGen ℂ (y t) (rot t) ∧
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S)[t] : ZMod S.m)),
∃ (hy : Function.Injective (fun t => Point.map p₀ (eY (y t)))),
∃ (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t))),
∃ (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S)[t] ∧ (g32p_exponents S)[t] < S.m),
∃ (hpair : ∀ i : Fin r,
      (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩] +
      (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] = S.m),
∃ (h : ℕ),
∃ (hh : 0 < h + 1),
∃ (q₀ : g3_power Y (h + 1) ⟶ W₀),
∃ inst17 : IsFinite q₀.left,
    let := inst17
∃ (hqsurj : Function.Surjective (Point.map q₀)),
∃ (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀),
∃ (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f),
∃ (γ : g3_power Z (h + 1) ⟶ B₀),
∃ inst18 : IsFinite γ.left,
    let := inst18
∃ (hγsurj : Function.Surjective (Point.map γ)),
∃ (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ),
∃ (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f),
∃ (β₀ : W₀ ⟶ B₀),
∃ inst19 : IsFinite β₀.left,
    let := inst19
∃ (hβ₀ : q₀ ≫ β₀ = s2_powerMap p₀ (h + 1) ≫ γ),
∃ (d₀ : W₀ ⟶ W₀),
∃ (hd₀ : d₀ ≫ β₀ = β₀),
∃ (hgenerator : q₀ ≫ d₀ =
      s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q₀),
∃ (C₀ : Over (Spec ↧ℂ)),
∃ inst20 : IsIntegral C₀.left,
    let := inst20
∃ inst21 : Smooth C₀.hom,
    let := inst21
∃ inst22 : IsProjective C₀.hom,
    let := inst22
∃ (P : g32p_Part J aut S),
∃ (qC : C₀ ⟶ Y),
∃ (jC : C₀ ⟶ J),
∃ (eC : C ≃ₜ ComplexPoint C₀),
∃ (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z),
∃ (hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x)),
∃ (hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z)),
∃ (hχ : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u),
∃ (hjC : Function.Bijective (homPullback jC 1)),
∃ (primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))),
∃ (hprimitive : ∀ v, homPullback qC 1 (primitive v) =
      homPullback jC 1 (homPullback P.proj 1 v)),
∃ (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1)),
∃ (hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m),
∃ (hselected : h + 1 = 2 * P.k),
∃ inst23 : ChartedSpace ℂ (rsq_Quot S.H C),
    let := inst23
∃ inst24 : IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C),
    let := inst24
∃ (hgenus : 2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
      (g32p_exponents S).length),
∃ (hr : r = 0),
    Etale β₀.left ∧
    ∃ hZ : SmoothOfRelativeDimension 1 Z.hom,
    let := hZ
    let PP : Over (Spec ↧ℂ) := Over.mk
      (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ))
    let X₀ := TopCat.of (ComplexPoint W₀)
    let H₀ := AlgebraicTopology.Singular.Cohomology ℚ X₀ (2 * P.k)
    ∃ (ℓ : PP ⟶ B₀), IsClosedImmersion ℓ.left ∧
      (∀ b : ComplexPoint B₀, b ∈ Set.range (Point.map ℓ) ↔
        ∃ z : Fin (h + 1) → ComplexPoint Z,
          Point.map γ (s2_lift (h + 1) z) = b ∧
          ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z), θ ≠ 0 ∧
            b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
              (hE := Module.finrank_fin_fun (n := 1) ℂ) θ = ∑ t, Finsupp.single (z t) (1 : ℤ)) ∧
    ∃ (Q : Over (Spec ↧ℂ)) (hQ : IsIntegral Q.left)
      (hQs : Smooth Q.hom) (hQp : IsProjective Q.hom),
    let := hQ
    let := hQs
    let := hQp
    ∃ (eQ : Q ≅ PP) (ι : Q ⟶ W₀),
      IsClosedImmersion ι.left ∧ ι ≫ β₀ = eQ.hom ≫ ℓ ∧
      (∀ s t : Fin S.m, s ≠ t → Disjoint
        (Set.range (ι ≫ (End.of d₀ ^ s.val).asHom).left)
        (Set.range (ι ≫ (End.of d₀ ^ t.val).asHom).left)) ∧
      (β₀.left ⁻¹' Set.range ℓ.left =
        ⋃ t : Fin S.m, Set.range (ι ≫ (End.of d₀ ^ t.val).asHom).left) ∧
      (∀ x : Q.left, ∃ U : Q.left.Opens, x ∈ U ∧
        Nonempty (Scheme.Modules.restrict (s2c_conormal ι.left) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin P.k) : U.toScheme.Modules))) ∧
      ∃ c, a3b4_IsCycleClass W₀.hom (s2e_componentCycle ι ℚ) P.k c ∧
      let cl := AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ _ (2 * P.k) c
      let HI := (s2e_hyperplaneIdeal P.k).comap eQ.hom.left
      let QH := s2c_subscheme Q HI
      let jH := s2c_subschemeι Q HI
      ∃ (hH : IsIntegral QH.left),
      let := hH
      ∃ cH, a3b4_IsCycleClass Q.hom (s2e_componentCycle jH ℚ) 1 cH ∧
      let H := AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ _ 2 cH
      s2e_normalEuler ι P.k c = (-1 : ℚ) ^ P.k •
        s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H P.k ∧
      s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H P.k ≠ 0 ∧
      (∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
        s2e_weightedSum S.m (fun t : ZMod S.m => ζ ^ t.val)
          (fun t : Fin S.m => TensorProduct.tmul ℚ (1 : ℂ)
            (s2e_pullback ℚ ((End.of d₀ ^ (S.m - t.val)).asHom) (2 * P.k) cl)) ≠ 0) ∧
    ∃ (a : Fin (Nat.totient S.m) → Fin S.m → ℚ)
      (v : Fin (Nat.totient S.m) → H₀),
      LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = LinearMap.ker
        (Polynomial.aeval (s2e_pullback ℚ d₀ (2 * P.k)) (Polynomial.cyclotomic S.m ℚ)) ∧
      (∀ j,
        let γ := s2e_rationalOrbitCycle ι d₀ S.m (a j)
        (∀ x ∈ γ.support, Order.coheight x = P.k) ∧
        ∃ cj, a3b4_IsCycleClass W₀.hom γ P.k cj ∧
          AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ _ _ cj = v j) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
        (∃ u : ℂ ⊗[ℚ] H₀, u ≠ 0 ∧
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u) ∧
        (∀ u : ℂ ⊗[ℚ] H₀,
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u →
          ∃ b : Fin (Nat.totient S.m) → ℂ,
            u = ∑ j, b j • TensorProduct.tmul ℚ (1 : ℂ) (v j))))) : type_of% hNative := hNative

example := @s4_chain_native_input_identity

end HodgeLean.Foundations.Program

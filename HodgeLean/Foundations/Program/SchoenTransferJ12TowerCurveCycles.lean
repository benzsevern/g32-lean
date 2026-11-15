import HodgeLean.Foundations.Program.SchoenTransferJ1Row3Proofs
import HodgeLean.Foundations.Program.SchoenTransferJ12QuotientCycles

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Papers
open scoped BigOperators Manifold ContDiff OnePoint TensorProduct
namespace HodgeLean.Foundations.Program

/-- The retained supported tower basis supplies cycles on its actual curve power. -/
theorem s4_selected_tower_curve_cycles
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
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S)[t] : ZMod S.m))
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t))))
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t)))
    (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S)[t] ∧ (g32p_exponents S)[t] < S.m)
    (hpair : ∀ i : Fin r,
      (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩] +
      (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] = S.m)
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
    (C₀ J : Over (Spec ↧ℂ))
    [IsIntegral C₀.left] [Smooth C₀.hom] [IsProjective C₀.hom]
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (P : g32p_Part J aut S)
    (qC : C₀ ⟶ Y) (jC : C₀ ⟶ J)
    (eC : C ≃ₜ ComplexPoint C₀) (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z)
    (hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x))
    (hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z))
    (hχ : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (hjC : Function.Bijective (homPullback jC 1))
    (primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hprimitive : ∀ v, homPullback qC 1 (primitive v : HQ Y 1) =
      homPullback jC 1 (homPullback P.proj 1 v))
    (hscalar : ∀ (u : S.H) (v : HQ P.P 1),
      homPullback (a ((QuotientGroup.mk u : S.H ⧸ S.χ.ker)⁻¹)) 1 (primitive v : HQ Y 1) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1))
    (hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m)
    (hselected : h + 1 = 2 * P.k)
    [ChartedSpace ℂ (rsq_Quot S.H C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C)]
    (hgenus : 2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
      (g32p_exponents S).length)
    (hExceptionalPrimitive : ∀ i : Fin r,
    let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let K := s2c_subscheme (B i.castSucc) I
    let kι := s2c_subschemeι (B i.castSucc) I
    let E := s2c_exceptional (b i) I
    let j : E ⟶ B i.succ := pullback.fst (b i) kι
    let _p : E ⟶ K := pullback.snd (b i) kι
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    ∀ (n : ℕ) (ζ : ℂ), IsPrimitiveRoot ζ S.m →
      ∀ v : AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint (s2b_preimage β j))) n,
        s2b_preimageCohomologyDeck β j (d i.succ) (hd i.succ) n v = ζ • v → v = 0)
    (W : Over (Spec ↧ℂ))
    (eWr : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W)
    (hS2 :
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
    letI := hft
    letI := hqc
    letI := hsep
    letI := hφ
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
    letI := hQ
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
            u = ∑ j, b j • TensorProduct.tmul ℚ (1 : ℂ) (v j))) :
    ∃ hInt : IsIntegral (g3_power Y (2 * P.k)).left,
      letI := hInt
      ∃ hSmooth : Smooth (g3_power Y (2 * P.k)).hom,
        letI := hSmooth
        ∃ hProjective : IsProjective (g3_power Y (2 * P.k)).hom,
          letI := hProjective
          s4_invariantPrimitive S Y a e (2 * P.k)
            (Nat.mul_pos (by norm_num) P.act.cyc_positive) ≤
            cfd_cycleSpan (g3_power Y (2 * P.k)) P.k := by
  have hSupport := s4_chain_selected_supported_basis_aux S Y Z W₀ B₀ hdimY hdimZ
    a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction
    r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq
    γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀
    htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd
    hdinit hdw horder C₀ J aut P qC jC eC eZ hqC hpC hχ hjC primitive
    hprimitive hscalar hrank hselected hgenus hExceptionalPrimitive W eWr hS2
  obtain ⟨tf, htf0, htfs, hft, hqc, hsep, hφqc, trr, tr₀, hpairr, hpair₀,
    hnormr, hnorm₀, transfer, hadjoint, hretract, hequiv,
    sliceQ, hSliceIntegral, sliceIso, lineMap, sliceι, hLine, hSlice,
    hComponent, hAvoid, coeff, basisv, hli, hspan, hclasses, heigen⟩ := hSupport
  letI := hft
  letI := hqc
  letI := hsep
  letI := hφqc
  letI := hSliceIntegral
  let powIntegral : IsIntegral (g3_power Y (2 * P.k)).left :=
    spec_g3b_isIntegral_power Y (2 * P.k)
  let powSmooth : Smooth (g3_power Y (2 * P.k)).hom := spec_g3_smooth_power Y (2 * P.k)
  let powProjective : IsProjective (g3_power Y (2 * P.k)).hom :=
    spec_g3c_isProjective_power Y (2 * P.k)
  letI := powIntegral
  letI := powSmooth
  letI := powProjective
  have hCurve := s4_selected_quotient_basis_cycles S Y hdimY (h + 1) P.k
    P.act.cyc_positive hh hselected a e ha1 hamul W₀ q₀ hqsurj hqinv hq d₀
    hgenerator basisv hspan (by
      intro i
      obtain ⟨cr, hcr, c₀, hc₀, htransfer, habs⟩ := (hclasses i).2.2
      exact ⟨a1p_pushforward (eWr.inv ≫ tf (Fin.last r)).left
        (s2e_rationalOrbitCycle sliceι (eWr.inv ≫ d (Fin.last r) ≫ eWr.hom)
          S.m (coeff i)), (hclasses i).2.1, c₀, hc₀, habs⟩)
  exact ⟨powIntegral, powSmooth, powProjective, hCurve⟩

#print axioms s4_selected_tower_curve_cycles

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCycleS3Proofs

/-! # S3 coherent slice tower
Implication from the retained paired supplier and blowup tower to a single
projective slice family with every transition identity and actual reduced
strict transform. Initial conormal and residual Cartier geometry enter the
assembly through their mathematical construction, with no extra binder.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program


/-- A paired integral slice has a unique successor with its transition and reduced strict-transform ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.3–2.5,
printed pp. 13–15; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_chain_slice_successor
    {Q B B' : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (b : B' ⟶ B) [IsSeparated b.left] (D₁ D₂ : B.left.IdealSheafData)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((D₁ ⊔ D₂).comap f.left).ideal U) ≃ₗ[Γ(T.left, U)]
          Γ(T.left, U))) → ∃! u : T ⟶ B', u ≫ b = f)
    (hambient : ∀ x : B'.left, ∃ U : B'.left.affineOpens, x ∈ U.1 ∧
      Nonempty ((((D₁ ⊔ D₂).comap b.left).ideal U) ≃ₗ[Γ(B'.left, U)] Γ(B'.left, U)))
    (ℓ : Q ⟶ B) [IsClosedImmersion ℓ.left]
    (hpair : D₁.comap ℓ.left = D₂.comap ℓ.left)
    (hCartier : ∀ x : Q.left, ∃ U : Q.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((D₁.comap ℓ.left).ideal U) ≃ₗ[Γ(Q.left, U)] Γ(Q.left, U))) :
    ∃! u : Q ⟶ B', u ≫ b = ℓ ∧ IsClosedImmersion u.left ∧
      u.left.ker = s2c_strictTransform b.left ℓ.left.ker (D₁ ⊔ D₂) ∧
      Disjoint (Set.range u.left)
        (((s2c_strictTransform b.left D₁ (D₁ ⊔ D₂)).support : Set B'.left) ∪
          ((s2c_strictTransform b.left D₂ (D₁ ⊔ D₂)).support : Set B'.left)) :=
  s2e_chain_slice_successor_aux b D₁ D₂ hblowup hambient ℓ hpair hCartier

example := @s2e_chain_slice_successor

/-- The successor avoids both newly processed reduced branch supports.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.3–2.5,
printed pp. 13–15; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_chain_slice_pair_removed
    {Q B B' : Scheme} (b : B' ⟶ B) (ℓ : Q ⟶ B) (u : Q ⟶ B')
    (hfac : u ≫ b = ℓ) (D₁ D₂ : B.IdealSheafData)
    (hpair : D₁.comap ℓ = D₂.comap ℓ)
    (hambient : ∀ x : B', ∃ U : B'.affineOpens, x ∈ U.1 ∧
      Nonempty ((((D₁ ⊔ D₂).comap b).ideal U) ≃ₗ[Γ(B', U)] Γ(B', U)))
    (hslice : ∀ q : Q, ∃ V : Q.affineOpens, q ∈ V.1 ∧
      Nonempty ((((D₁ ⊔ D₂).comap ℓ).ideal V) ≃ₗ[Γ(Q, V)] Γ(Q, V))) :
    Disjoint (Set.range u)
      (((s2c_strictTransform b D₁ (D₁ ⊔ D₂)).support : Set B') ∪
        ((s2c_strictTransform b D₂ (D₁ ⊔ D₂)).support : Set B')) :=
  s2e_chain_slice_pair_removed_aux b ℓ u hfac D₁ D₂ hpair hambient hslice

example := @s2e_chain_slice_pair_removed

/-- The prescribed initial coordinate slice extends to one family retaining every transition,
immersion, strict-transform identity and new-pair avoidance.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.3–2.5,
printed pp. 13–15; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_chain_slice_all_levels
    (k r : ℕ) (ι : Fin r ↪ Fin (k + 1))
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    [∀ i, IsSeparated (b i).left]
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
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
    (ℓ₀ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B 0)
    [IsClosedImmersion ℓ₀.left]
    (hresidue : ∀ j : Fin r,
      (D 0 ⟨2 * j.val, by omega⟩).comap ℓ₀.left = s2e_s2b_residueIdeal k (ι j) ∧
      (D 0 ⟨2 * j.val + 1, by omega⟩).comap ℓ₀.left = s2e_s2b_residueIdeal k (ι j)) :
    let PP : Over (Spec ↧ℂ) :=
      Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    ∃ ℓ : ∀ i, PP ⟶ B i,
      ℓ 0 = ℓ₀ ∧
      (∀ i, IsClosedImmersion (ℓ i).left) ∧
      (∀ i : Fin r, ℓ i.succ ≫ b i = ℓ i.castSucc) ∧
      (∀ i : Fin r, (ℓ i.succ).left.ker =
        s2c_strictTransform (b i).left (ℓ i.castSucc).left.ker
          (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
            D i.castSucc ⟨2 * i.val + 1, by omega⟩)) ∧
      (∀ (i : Fin r) (t : Fin (2 * r)),
        2 * i.val ≤ t.val → t.val < 2 * (i.val + 1) →
          Disjoint (Set.range (ℓ i.succ).left) (D i.succ t).support) :=
  s2e_chain_slice_all_levels_aux k r ι B b D htransform hcartier hblowup ℓ₀ hresidue

example := @s2e_chain_slice_all_levels

/-- Every processed branch avoids the same slice family at every later level.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.3–2.5,
printed pp. 13–15; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_chain_slice_avoidance_all_levels
    {r : ℕ} {Q : Scheme} (B : Fin (r + 1) → Scheme)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (ℓ : ∀ i, Q ⟶ B i)
    (hfac : ∀ i : Fin r, ℓ i.succ ≫ b i = ℓ i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).IdealSheafData)
    (K : ∀ i : Fin r, (B i.castSucc).IdealSheafData)
    (htransform : ∀ (i : Fin r) t,
      D i.succ t = s2c_strictTransform (b i) (D i.castSucc t) (K i))
    (hnew : ∀ (i : Fin r) (t : Fin (2 * r)),
      2 * i.val ≤ t.val → t.val < 2 * (i.val + 1) →
      Disjoint (Set.range (ℓ i.succ)) ((D i.succ t).support : Set (B i.succ))) :
    ∀ (i : Fin (r + 1)) (t : Fin (2 * r)), t.val < 2 * i.val →
      Disjoint (Set.range (ℓ i)) ((D i t).support : Set (B i)) :=
  s2e_chain_slice_avoidance_all_levels_aux B b ℓ hfac D K htransform hnew

example := @s2e_chain_slice_avoidance_all_levels

/-- The retained supplier yields the exact projective slice, intersections, conormal ranks and branch avoidance.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.3–2.5,
printed pp. 13–15; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_projective_slice
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
    (hprimitive : ∀ v, homPullback qC 1 (primitive v) =
      homPullback jC 1 (homPullback P.proj 1 v))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1))
    (hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m)
    (hselected : h + 1 = 2 * P.k)
    [ChartedSpace ℂ (rsq_Quot S.H C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C)]
    (hgenus : 2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
      (g32p_exponents S).length)
    (hr : 0 < r) :
    let PP : Over (Spec ↧ℂ) :=
      Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ))
    ∃ ℓ : ∀ i, PP ⟶ B i,
      (∀ i, IsClosedImmersion (ℓ i).left) ∧
      (∀ i : Fin r, ℓ i.succ ≫ b i = ℓ i.castSucc) ∧
      (∀ i : Fin r, (ℓ i.succ).left.ker =
        s2c_strictTransform (b i).left (ℓ i.castSucc).left.ker
          (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
            D i.castSucc ⟨2 * i.val + 1, by omega⟩)) ∧
      (∀ i : Fin r,
        (D 0 ⟨2 * i.val, by omega⟩).comap (ℓ 0).left =
          (D 0 ⟨2 * i.val + 1, by omega⟩).comap (ℓ 0).left) ∧
      (∀ T : Finset (Fin r),
        let I := T.sup (fun i =>
          (D 0 ⟨2 * i.val, by omega⟩).comap (ℓ 0).left)
        (T.card ≤ P.k → Nonempty (s2c_subscheme PP I ≅
          Over.mk (ProjectiveSpace.toBase (Fin (P.k - T.card + 1)) (Spec ↧ℂ)))) ∧
        (P.k < T.card → IsEmpty (s2c_subscheme PP I).left) ∧
        (∀ x : (s2c_subscheme PP I).left,
          ∃ U : (s2c_subscheme PP I).left.Opens, x ∈ U ∧
            Nonempty (Scheme.Modules.restrict
              (s2c_conormal (s2c_subschemeι PP I).left) U.ι ≅
              (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin T.card) :
                U.toScheme.Modules)))) ∧
      (∀ (i : Fin (r + 1)) (t : Fin (2 * r)), t.val < 2 * i.val →
        Disjoint (Set.range (ℓ i).left) (D i t).support) :=
  s2e_projective_slice_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder C₀ J aut P qC jC eC eZ hqC hpC hχ hjC primitive hprimitive hscalar hrank hselected hgenus hr

example := @s2e_projective_slice

end HodgeLean.Foundations.Program

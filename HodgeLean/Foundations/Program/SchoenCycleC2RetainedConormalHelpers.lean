import HodgeLean.Foundations.Program.SchoenCycleC2RetainedCoheightHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2EtaleConormalFramesHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- Every actual retained forward component has local conormal frames
with the rank fixed by its projective model and retained tower dimension. -/
theorem s2e_retained_component_conormal_frames
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
    (k : ℕ) (hselected : h + 1 = 2 * k)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B (Fin.last r))
    (hℓ : IsClosedImmersion ℓ.left)
    (havoid : ∀ t, Disjoint (Set.range ℓ.left) (D (Fin.last r) t).support)
    (W : Over (Spec ↧ℂ))
    (eWr : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W)
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left]
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (ι : Q ⟶ W) (hι : IsClosedImmersion ι.left)
    (hproj : ι ≫ (eWr.inv ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))) =
      eQ.hom ≫ ℓ) :
    let δ := eWr.inv ≫ d (Fin.last r) ≫ eWr.hom
    ∀ t : Fin S.m, ∀ x : Q.left, ∃ U : Q.left.Opens, x ∈ U ∧
      Nonempty (Scheme.Modules.restrict
        (s2c_conormal (ι ≫ (End.of δ ^ t.val).asHom).left) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules)) := by
  let : IsClosedImmersion ℓ.left := hℓ
  let : IsClosedImmersion ι.left := hι
  obtain ⟨U, hU, _, he⟩ :=
    s2e_chain_cover_etale_near_slice S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eWr.symm k ℓ havoid
  let β := eWr.inv ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))
  let δ := eWr.inv ≫ d (Fin.last r) ≫ eWr.hom
  have hδβ : δ ≫ β = β := by
    dsimp only [δ, β]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hd]
  have hPPSmooth : Smooth
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
    s0_projective_space_smooth k (Spec ↧ℂ)
  have hQSmooth : Smooth Q.hom := by
    rw [← Over.w eQ.hom]
    infer_instance
  letI : SmoothOfRelativeDimension k Q.hom := by
    have hq := (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Q.left) Q.hom)
    rw [s2e_projective_model_dimension Q k eQ] at hq
    exact hq
  have hdimB : TopologicalSpace.dim (B (Fin.last r)).left = 2 * k :=
    (s2e_retained_tower_dimension Z B₀ hdimZ (h + 1) r γ hγsurj
      B e₀ b D hcartier hblowup (Fin.last r)).trans hselected
  letI : SmoothOfRelativeDimension (k + k) (B (Fin.last r)).hom := by
    have hb := (inferInstance : SmoothOfRelativeDimension
      (TopologicalSpace.dim (B (Fin.last r)).left) (B (Fin.last r)).hom)
    rw [hdimB, two_mul] at hb
    exact hb
  letI : IsIso (d (Fin.last r)) :=
    (isUnit_iff_isIso _).mp (IsUnit.of_pow_eq_one (horder (Fin.last r)) (NeZero.ne S.m))
  letI : IsIso δ := by
    dsimp only [δ]
    infer_instance
  have hunit : IsUnit (End.of δ) := (isUnit_iff_isIso _).mpr inferInstance
  dsimp only
  intro t
  letI : IsIso (End.of δ ^ t.val).asHom := (isUnit_iff_isIso _).mp (hunit.pow t.val)
  letI : IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left := by
    change IsClosedImmersion (ι.left ≫ (End.of δ ^ t.val).asHom.left)
    infer_instance
  apply s2e_etale_neighbourhood_conormal_frames Q W (B (Fin.last r)) k k
    (ι ≫ (End.of δ ^ t.val).asHom) β U ?_ he
  rw [Category.assoc, s2e_power_projection δ β hδβ t.val, hproj]
  rintro _ ⟨x, rfl⟩
  exact hU ⟨eQ.hom.left x, rfl⟩

end HodgeLean.Foundations.Program

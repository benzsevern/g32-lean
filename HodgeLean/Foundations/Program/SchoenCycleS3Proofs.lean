import HodgeLean.Foundations.Program.SchoenCycleS3Initial
import HodgeLean.Foundations.Program.SchoenCycleS3Links
import HodgeLean.Foundations.Program.SchoenCycleCartierAvoidance
import HodgeLean.Foundations.Program.SchoenCycleS1c
import HodgeLean.Foundations.Program.SchoenCycleS2
import HodgeLean.Foundations.Program.SchoenCycleS2b
import HodgeLean.Foundations.Program.SchoenCycleStageDefs
import HodgeLean.Foundations.Program.SchoenTowerFibreDefs
import HodgeLean.Foundations.Program.SchoenTowerSheafDefs

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

theorem s2e_chain_slice_successor_aux
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
          ((s2c_strictTransform b.left D₂ (D₁ ⊔ D₂)).support : Set B'.left)) := by
  exact s2e_paired_blowup_slice_strict_lift_avoiding_branches b D₁ D₂
    hblowup hambient ℓ hpair hCartier

theorem s2e_chain_slice_pair_removed_aux
    {Q B B' : Scheme} (b : B' ⟶ B) (ℓ : Q ⟶ B) (u : Q ⟶ B')
    (hfac : u ≫ b = ℓ) (D₁ D₂ : B.IdealSheafData)
    (hpair : D₁.comap ℓ = D₂.comap ℓ)
    (hambient : ∀ x : B', ∃ U : B'.affineOpens, x ∈ U.1 ∧
      Nonempty ((((D₁ ⊔ D₂).comap b).ideal U) ≃ₗ[Γ(B', U)] Γ(B', U)))
    (hslice : ∀ q : Q, ∃ V : Q.affineOpens, q ∈ V.1 ∧
      Nonempty ((((D₁ ⊔ D₂).comap ℓ).ideal V) ≃ₗ[Γ(Q, V)] Γ(Q, V))) :
    Disjoint (Set.range u)
      (((s2c_strictTransform b D₁ (D₁ ⊔ D₂)).support : Set B') ∪
        ((s2c_strictTransform b D₂ (D₁ ⊔ D₂)).support : Set B')) := by
  exact s2e_lifted_pair_strict_branch_avoidance b ℓ u hfac D₁ D₂ hpair hambient hslice

theorem s2e_chain_slice_all_levels_aux
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
          Disjoint (Set.range (ℓ i.succ).left) (D i.succ t).support) := by
  classical
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  letI : IsIntegral PP.left := IntersectionProductScaf_projective_integral k
  have hp : ∀ (n : ℕ) (hn : n ≤ r),
      ∃ ℓ : ∀ i : Fin (n + 1), PP ⟶ B ⟨i.val, by omega⟩,
        ℓ 0 = ℓ₀ ∧
        (∀ i, IsClosedImmersion (ℓ i).left) ∧
        (∀ i : Fin n, ℓ i.succ ≫ b ⟨i.val, by omega⟩ = ℓ i.castSucc) ∧
        (∀ i : Fin n, (ℓ i.succ).left.ker =
          s2c_strictTransform (b ⟨i.val, by omega⟩).left (ℓ i.castSucc).left.ker
            (D ⟨i.val, by omega⟩ ⟨2 * i.val, by omega⟩ ⊔
              D ⟨i.val, by omega⟩ ⟨2 * i.val + 1, by omega⟩)) ∧
        (∀ (i : Fin n) (t : Fin (2 * r)),
          2 * i.val ≤ t.val → t.val < 2 * (i.val + 1) →
            Disjoint (Set.range (ℓ i.succ).left)
              ((D ⟨i.succ.val, by omega⟩ t).support : Set (B ⟨i.succ.val, by omega⟩).left)) := by
    intro n
    induction n with
    | zero =>
        intro hn
        refine ⟨Fin.cases ℓ₀ (fun i => Fin.elim0 i), rfl, ?_, ?_, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun i => Fin.elim0 i) i
          simpa only [Fin.cases_zero] using (inferInstance : IsClosedImmersion ℓ₀.left)
        · intro i; exact Fin.elim0 i
        · intro i; exact Fin.elim0 i
        · intro i; exact Fin.elim0 i
    | succ n ih =>
        intro hn
        obtain ⟨ℓ, hzero, himm, hfac, hker, hnew⟩ := ih (by omega)
        let j : Fin r := ⟨n, by omega⟩
        have hres := s2e_chain_unprocessed_pair_transverse k r n (by omega) ι
          (fun i => B ⟨i.val, by omega⟩)
          (fun i => b ⟨i.val, by omega⟩)
          (fun i => D ⟨i.val, by omega⟩)
          (fun i t => htransform ⟨i.val, by omega⟩ t)
          (fun i => hcartier ⟨i.val, by omega⟩) ℓ hfac
          (by intro j; simpa only [Fin.val_zero, Fin.mk_zero, hzero] using hresidue j) j (by rfl)
        change (D j.castSucc ⟨2 * n, by omega⟩).comap (ℓ (Fin.last n)).left = _ ∧
          (D j.castSucc ⟨2 * n + 1, by omega⟩).comap (ℓ (Fin.last n)).left = _ at hres
        haveI := himm (Fin.last n)
        obtain ⟨u, ⟨hu, hui, huk, hua⟩, _⟩ :=
          s2e_chain_slice_successor_aux (b j)
            (D j.castSucc ⟨2 * n, by omega⟩)
            (D j.castSucc ⟨2 * n + 1, by omega⟩)
            (hblowup j) (hcartier j) (ℓ (Fin.last n))
            (hres.1.trans hres.2.symm)
            (by rw [hres.1]; exact s2e_chain_pair_cartier_on_slice k (ι j))
        let ℓ' : ∀ i : Fin (n + 1 + 1), PP ⟶ B ⟨i.val, by omega⟩ :=
          Fin.lastCases u ℓ
        have hcast (i : Fin (n + 1)) : ℓ' i.castSucc = ℓ i :=
          Fin.lastCases_castSucc i
        have hlast : ℓ' (Fin.last (n + 1)) = u := Fin.lastCases_last
        refine ⟨ℓ', ?_, ?_, ?_, ?_, ?_⟩
        · exact (hcast 0).trans hzero
        · intro i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · rw [hlast]; exact hui
          · rw [hcast]; exact himm i
        · intro i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · change ℓ' (Fin.last (n + 1)) ≫ b j = ℓ' (Fin.last n).castSucc
            rw [hlast, hcast]; exact hu
          · change ℓ' i.succ.castSucc ≫ b ⟨i.val, by omega⟩ = ℓ' i.castSucc.castSucc
            rw [hcast, hcast]; exact hfac i
        · intro i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · change (ℓ' (Fin.last (n + 1))).left.ker = _
            rw [hlast, hcast]; exact huk
          · change (ℓ' i.succ.castSucc).left.ker = _
            rw [hcast, hcast]; exact hker i
        · intro i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · intro t ht ht'
            change Disjoint (Set.range (ℓ' (Fin.last (n + 1))).left) _
            rw [hlast]
            change Disjoint (Set.range u.left) ((D j.succ t).support : Set _)
            change 2 * n ≤ t.val at ht
            change t.val < 2 * (n + 1) at ht'
            by_cases ht0 : t.val = 2 * n
            · have he : t = (⟨2 * n, by omega⟩ : Fin (2 * r)) := Fin.ext ht0
              rw [he, htransform j]
              exact (disjoint_sup_right.mp hua).1
            · have he : t = (⟨2 * n + 1, by omega⟩ : Fin (2 * r)) :=
                Fin.ext (show t.val = 2 * n + 1 by omega)
              rw [he, htransform j]
              exact (disjoint_sup_right.mp hua).2
          · intro t ht ht'
            change Disjoint (Set.range (ℓ' i.succ.castSucc).left) _
            rw [hcast]; exact hnew i t ht ht'
  exact hp r le_rfl


theorem s2e_chain_slice_avoidance_all_levels_aux
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
      Disjoint (Set.range (ℓ i)) ((D i t).support : Set (B i)) := by
  exact s2e_processed_branches_avoid_tower B b ℓ hfac D K htransform hnew

theorem s2e_projective_slice_aux
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
        Disjoint (Set.range (ℓ i).left) (D i t).support) := by
  classical
  letI : SmoothOfRelativeDimension 1 Z.hom := s2e_scheme_curve_relativeDimension Z hdimZ
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
    b3_holForm_finiteDimensional (Module.finrank_fin_fun (n := 1) ℂ)
  have hlen : (g32p_exponents S).length = 2 * r := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr σ).symm
  have hg : 2 * P.k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r := by
    rw [← s2e_scheme_holForm_finrank_homeomorph Z eZ]
    omega
  let yz : Fin (2 * r) → ComplexPoint Z := fun t => Point.map p₀ (eY (y (σ t)))
  have hyz : Function.Injective yz := hy.comp σ.injective
  obtain ⟨w, hw, hout, hres, _, _⟩ := s2e_paired_slice_differential_family
    (Module.finrank_fin_fun (n := 1) ℂ) P.k r yz hyz hg
  have hd : Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = P.k + 1 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun]
    omega
  have hout' : ∀ i p, p ∉ Set.range yz → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0 := by
    intro i p hp
    exact hout i p (fun he => hp ⟨_, he.symm⟩) (fun he => hp ⟨_, he.symm⟩)
  let γ' : g3_power Z (2 * P.k) ⟶ B₀ :=
    eqToHom (congrArg (g3_power Z) hselected.symm) ≫ γ
  letI : IsFinite γ'.left := by
    dsimp only [γ', Over.comp_left]
    infer_instance
  obtain ⟨hγ', hγsurj', hγquot'⟩ := s2e_symmetric_quotient_reindex Z B₀
    (h + 1) (2 * P.k) hselected.symm γ hγinv hγsurj hγ
  obtain ⟨ι, ℓbase, himm, hbase⟩ := s2e_initial_slice_coordinate_restrictions Z B₀
    P.k r hr yz hyz w (fun i j => (hres i j).2) hw hout' hg hd γ'
    hγ' hγsurj' hγquot' (fun i j => (hres i j).1) h hselected.symm
  have hround : eqToHom (congrArg (g3_power Z) hselected) ≫ γ' = γ := by
    simp only [γ', ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rw [hround] at hbase
  let ℓ₀ := ℓbase ≫ e₀.inv
  have hinit : ℓ₀ ≫ e₀.hom = ℓbase := by simp only [ℓ₀, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  haveI : IsClosedImmersion ℓ₀.left := by
    haveI := himm
    change IsClosedImmersion (ℓbase.left ≫ e₀.inv.left)
    infer_instance
  have hres₀ : ∀ j : Fin r,
      (D 0 ⟨2 * j.val, by omega⟩).comap ℓ₀.left = s2e_s2b_residueIdeal P.k (ι j) ∧
      (D 0 ⟨2 * j.val + 1, by omega⟩).comap ℓ₀.left = s2e_s2b_residueIdeal P.k (ι j) := by
    intro j
    have hinit' : ℓ₀.left ≫ e₀.hom.left = ℓbase.left := congrArg Over.Hom.left hinit
    rw [hD₀, hD₀, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, hinit']
    exact hbase j
  letI : ∀ i, IsSeparated (b i).left := fun i => by
    haveI : IsSeparated ((b i).left ≫ (B i.castSucc).hom) := by
      rw [Over.w]; infer_instance
    exact IsSeparated.of_comp (b i).left (B i.castSucc).hom
  obtain ⟨ℓ, hzero, hclosed, hfac, hker, hnew⟩ := s2e_chain_slice_all_levels_aux
    P.k r ι B b D htransform hcartier hblowup ℓ₀ hres₀
  refine ⟨ℓ, hclosed, hfac, hker, ?_, ?_, ?_⟩
  · intro j
    rw [hzero]
    exact (hres₀ j).1.trans (hres₀ j).2.symm
  · intro T
    have hI : T.sup (fun j => (D 0 ⟨2 * j.val, by omega⟩).comap (ℓ 0).left) =
        s2e_s2b_intersectionIdeal P.k (T.map ι) := by
      rw [hzero]
      simp only [(hres₀ _).1]
      exact s2e_residue_intersection_reindex P.k r ι T
    dsimp only
    rw [hI]
    refine ⟨?_, ?_, ?_⟩
    · intro hT
      have hT' : (T.map ι).card ≤ P.k := by simpa only [Finset.card_map] using hT
      have hc := s2e_chain_residue_intersection_over_base P.k (T.map ι) hT'
      rw [Finset.card_map] at hc
      exact hc
    · intro hT
      exact s2e_chain_residue_projective_empty P.k (T.map ι)
        (by simpa only [Finset.card_map] using hT)
    · simpa only [Finset.card_map] using s2e_chain_residue_conormal P.k (T.map ι)
  · exact s2e_chain_slice_avoidance_all_levels_aux (fun i => (B i).left)
      (fun i => (b i).left) (fun i => (ℓ i).left)
      (fun i => congrArg Over.Hom.left (hfac i)) D
      (fun i => D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩) htransform hnew

end HodgeLean.Foundations.Program

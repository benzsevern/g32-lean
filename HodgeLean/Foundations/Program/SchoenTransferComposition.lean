import HodgeLean.Foundations.Program.SchoenTransferCorrespondence
import HodgeLean.Foundations.Program.CycleFoundations
import HodgeLean.Foundations.Program.CycleFoundationsPullback
import HodgeLean.Foundations.Program.CycleFoundationsSpans

/-! Algebraicity of the three-factor composition kernel. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped CategoryTheory.MonObj TensorProduct DirectSum
attribute [local irreducible] cupProductOf homPullback algebraicCycleClassSpan
namespace HodgeLean.Foundations.Program

/-- Exchange the two right factors with the graded cup-product sign. -/
theorem s4_cup_right_exchange
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (P : CupProduct X) (i j k : ℕ) (a : HQ X i) (b : HQ X j) (c : HQ X k) :
    P.cup (show (i + j) + k = (i + k) + j by omega) (P.cup rfl a b) c =
      ((-1 : ℚ) ^ (j * k)) • P.cup rfl (P.cup rfl a c) b := by
  rw [P.assoc rfl (show j + k = k + j by omega) (by omega) (by omega),
    P.graded_comm rfl (show j + k = k + j by omega) c b,
    map_smul, ← P.assoc rfl rfl rfl (by omega), Nat.mul_comm k j]

/-- Reorder four cup factors by exchanging the middle block with the last factor. -/
theorem s4_cup_four_exchange
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (P : CupProduct X) (u v s t l : ℕ) (hvs : v + s = l)
    {ut uv st m : ℕ} (hut : u + t = ut) (huv : u + v = uv) (hst : s + t = st) (h : uv + st = m)
    (a : HQ X u) (b : HQ X v) (c : HQ X s) (e : HQ X t) :
    P.cup h (P.cup huv a b) (P.cup hst c e) =
      ((-1 : ℚ) ^ (l * t)) •
        P.cup (show ut + l = m by omega)
          (P.cup hut a e) (P.cup hvs b c) := by
  subst ut
  subst uv
  subst st
  subst m
  rw [P.assoc rfl rfl rfl (by omega) a b (P.cup rfl c e),
    ← P.assoc hvs rfl (by omega) rfl b c e,
    P.graded_comm (by omega) (by omega) e (P.cup hvs b c),
    map_smul, ← P.assoc rfl (by omega) (by omega) (by omega) a e (P.cup hvs b c),
    Nat.mul_comm t l]

/-- Projection integration is natural in its retained factor. -/
theorem s4_projection_baseChange
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (C : Over (Spec ↧ℂ)) [GrpObj C] [IsCommMonObj C]
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (d : ℕ) (hdim : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (u : C ⟶ A) (n : ℕ)
    (z : HQ (A ⊗ B) (n + 2 * d)) :
    homPullback u n (cfd_projection A B d I n z) =
      cfd_projection C B d I n
        (homPullback (lift (fst C B ≫ u) (snd C B)) (n + 2 * d) z) := by
  classical
  let f := lift (fst C B ≫ u) (snd C B)
  let L := (homPullback u n).comp (cfd_projection A B d I n)
  let R := (cfd_projection C B d I n).comp (homPullback f (n + 2 * d))
  have he : L.comp (cp_kunnethMap A B (n + 2 * d)) =
      R.comp (cp_kunnethMap A B (n + 2 * d)) := by
    apply DirectSum.linearMap_ext ℚ
    intro k
    apply TensorProduct.ext'
    intro a b
    rcases k with ⟨⟨s, t⟩, hk⟩
    have hst : s + t = n + 2 * d := Finset.HasAntidiagonal.mem_antidiagonal.mp hk
    simp only [LinearMap.comp_apply, cp_kunnethMap, DirectSum.toModule_lof,
      TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    change homPullback u n
      (cfd_projection A B d I n ((cupProductOf (A ⊗ B)).cup hst
        (homPullback (fst A B) s a) (homPullback (snd A B) t b))) =
      cfd_projection C B d I n
        (homPullback f (n + 2 * d) ((cupProductOf (A ⊗ B)).cup hst
          (homPullback (fst A B) s a) (homPullback (snd A B) t b)))
    have hf : homPullback f s (homPullback (fst A B) s a) =
        homPullback (fst C B) s (homPullback u s a) := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_fst,
        spec_homPullback_comp, LinearMap.comp_apply]
    have hs : homPullback f t (homPullback (snd A B) t b) =
        homPullback (snd C B) t b := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd]
    rw [spec_homPullback_cup, hf, hs]
    by_cases ht : t = 2 * d
    · subst t
      have hn : s = n := by omega
      subst s
      rw [cfd_projection_cross A B d hdim I n,
        cfd_projection_cross C B d hdim I n, map_smul]
    · rw [cfd_projection_cross_off A B d I n s t hst ht,
        cfd_projection_cross_off C B d I n s t hst ht, map_zero]
  obtain ⟨w, rfl⟩ := (cp_kunneth A B (n + 2 * d)).surjective z
  exact LinearMap.congr_fun he w

/-- Cup product from the retained factor commutes with projection integration. -/
theorem s4_projection_cup_left
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hdim : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (n m : ℕ)
    (a : HQ A n) (z : HQ (A ⊗ B) (m + 2 * d)) :
    cfd_projection A B d I (n + m)
      ((cupProductOf (A ⊗ B)).cup (by omega)
        (homPullback (fst A B) n a) z) =
      (cupProductOf A).cup rfl a (cfd_projection A B d I m z) := by
  classical
  let L := (cfd_projection A B d I (n + m)).comp
    ((cupProductOf (A ⊗ B)).cup (show n + (m + 2 * d) = (n + m) + 2 * d by omega)
      (homPullback (fst A B) n a))
  let R := ((cupProductOf A).cup rfl a).comp (cfd_projection A B d I m)
  have he : L.comp (cp_kunnethMap A B (m + 2 * d)) =
      R.comp (cp_kunnethMap A B (m + 2 * d)) := by
    apply DirectSum.linearMap_ext ℚ
    intro k
    apply TensorProduct.ext'
    intro b c
    rcases k with ⟨⟨s, t⟩, hk⟩
    have hst : s + t = m + 2 * d := Finset.HasAntidiagonal.mem_antidiagonal.mp hk
    simp only [LinearMap.comp_apply, cp_kunnethMap, DirectSum.toModule_lof,
      TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    change cfd_projection A B d I (n + m)
      ((cupProductOf (A ⊗ B)).cup (by omega) (homPullback (fst A B) n a)
        ((cupProductOf (A ⊗ B)).cup hst
          (homPullback (fst A B) s b) (homPullback (snd A B) t c))) =
      (cupProductOf A).cup rfl a
        (cfd_projection A B d I m ((cupProductOf (A ⊗ B)).cup hst
          (homPullback (fst A B) s b) (homPullback (snd A B) t c)))
    rw [← (cupProductOf (A ⊗ B)).assoc rfl hst (by omega) (by omega),
      ← spec_homPullback_cup (fst A B) rfl]
    by_cases ht : t = 2 * d
    · subst t
      have hs : s = m := by omega
      subst s
      rw [cfd_projection_cross A B d hdim I (n + m),
        cfd_projection_cross A B d hdim I m, map_smul]
    · rw [cfd_projection_cross_off A B d I (n + m) (n + s) t (by omega) ht,
        cfd_projection_cross_off A B d I m s t hst ht, map_zero]
  obtain ⟨w, rfl⟩ := (cp_kunneth A B (m + 2 * d)).surjective z
  exact LinearMap.congr_fun he w

theorem s4_composite_kernel_algebraic
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (C : Over (Spec ↧ℂ)) [GrpObj C] [IsCommMonObj C]
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (d : ℕ) (hdim : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c₁ c₂ q : ℕ)
    (h : 2 * (c₁ + c₂) = 2 * q + 2 * d)
    (ξ : HQ (A ⊗ B) (2 * c₁)) (hξ : ξ ∈ cfd_cycleSpan (A ⊗ B) c₁)
    (κ : HQ (B ⊗ C) (2 * c₂)) (hκ : κ ∈ cfd_cycleSpan (B ⊗ C) c₂) :
    let T := (A ⊗ C) ⊗ B
    let f : T ⟶ A ⊗ B := lift (fst (A ⊗ C) B ≫ fst A C) (snd (A ⊗ C) B)
    let g : T ⟶ B ⊗ C := lift (snd (A ⊗ C) B) (fst (A ⊗ C) B ≫ snd A C)
    cfd_projection (A ⊗ C) B d I (2 * q)
      (HQ.castEquiv T h ((cupProductOf T).cup (by omega)
        (homPullback f (2 * c₁) ξ) (homPullback g (2 * c₂) κ))) ∈
      cfd_cycleSpan (A ⊗ C) q := by
  dsimp only
  let T := (A ⊗ C) ⊗ B
  let f : T ⟶ A ⊗ B := lift (fst (A ⊗ C) B ≫ fst A C) (snd (A ⊗ C) B)
  let g : T ⟶ B ⊗ C := lift (snd (A ⊗ C) B) (fst (A ⊗ C) B ≫ snd A C)
  letI : IsMonHom f := by dsimp only [f]; infer_instance
  letI : IsMonHom g := by dsimp only [g]; infer_instance
  have hξ' := cfd_hom_pullback_span (A ⊗ B) T f c₁ ξ hξ
  have hκ' := cfd_hom_pullback_span (B ⊗ C) T g c₂ κ hκ
  have hprod := (hc9k_cycleClassMultiplicative T).mem
    (show 2 * c₁ + 2 * c₂ = 2 * (c₁ + c₂) by omega) _ _ hξ' hκ'
  exact cfd_projection_span (A ⊗ C) B d hdim I (c₁ + c₂) q h _ hprod

/-- Integrating two separated kernels contracts precisely their shared factor. -/
theorem s4_composite_kernel_cross
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (C : Over (Spec ↧ℂ)) [GrpObj C] [IsCommMonObj C]
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (d : ℕ) (hdim : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (u v s t n : ℕ) (hvs : v + s = 2 * d) (hut : u + t = n)
    {uv st : ℕ} (huv : u + v = uv) (hst : s + t = st)
    (a : HQ A u) (b : HQ B v) (c : HQ B s) (e : HQ C t) :
    let T := (A ⊗ C) ⊗ B
    let f : T ⟶ A ⊗ B := lift (fst (A ⊗ C) B ≫ fst A C) (snd (A ⊗ C) B)
    let g : T ⟶ B ⊗ C := lift (snd (A ⊗ C) B) (fst (A ⊗ C) B ≫ snd A C)
    cfd_projection (A ⊗ C) B d I n
      ((cupProductOf T).cup (by omega)
        (homPullback f uv ((cupProductOf (A ⊗ B)).cup huv
          (homPullback (fst A B) u a) (homPullback (snd A B) v b)))
        (homPullback g st ((cupProductOf (B ⊗ C)).cup hst
          (homPullback (fst B C) s c) (homPullback (snd B C) t e)))) =
      I ((cupProductOf B).cup hvs b c) •
        (cupProductOf (A ⊗ C)).cup hut
          (homPullback (fst A C) u a) (homPullback (snd A C) t e) := by
  dsimp only
  let T := (A ⊗ C) ⊗ B
  let f : T ⟶ A ⊗ B := lift (fst (A ⊗ C) B ≫ fst A C) (snd (A ⊗ C) B)
  let g : T ⟶ B ⊗ C := lift (snd (A ⊗ C) B) (fst (A ⊗ C) B ≫ snd A C)
  have hfA : homPullback f u (homPullback (fst A B) u a) =
      homPullback (fst (A ⊗ C) B) u (homPullback (fst A C) u a) := by
    dsimp only [f]
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_fst,
      spec_homPullback_comp, LinearMap.comp_apply]
  have hfB : homPullback f v (homPullback (snd A B) v b) =
      homPullback (snd (A ⊗ C) B) v b := by
    dsimp only [f]
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd]
  have hgB : homPullback g s (homPullback (fst B C) s c) =
      homPullback (snd (A ⊗ C) B) s c := by
    dsimp only [g]
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_fst]
  have hgC : homPullback g t (homPullback (snd B C) t e) =
      homPullback (fst (A ⊗ C) B) t (homPullback (snd A C) t e) := by
    dsimp only [g]
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd,
      spec_homPullback_comp, LinearMap.comp_apply]
  rw [spec_homPullback_cup, spec_homPullback_cup, hfA, hfB, hgB, hgC,
    s4_cup_four_exchange T (cupProductOf T) u v s t (2 * d) hvs hut huv hst (by omega)]
  have hsign : (-1 : ℚ) ^ ((2 * d) * t) = 1 := by
    rw [Nat.mul_assoc, pow_mul]
    norm_num
  rw [hsign, one_smul,
    ← spec_homPullback_cup (fst (A ⊗ C) B) hut,
    ← spec_homPullback_cup (snd (A ⊗ C) B) hvs,
    cfd_projection_cross (A ⊗ C) B d hdim I n]

/-- A composite separated kernel vanishes away from the top shared degree. -/
theorem s4_composite_kernel_cross_off
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (C : Over (Spec ↧ℂ)) [GrpObj C] [IsCommMonObj C]
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (d : ℕ)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (u v s t n : ℕ) {uv st : ℕ} (h : uv + st = n + 2 * d)
    (hne : v + s ≠ 2 * d) (huv : u + v = uv) (hst : s + t = st)
    (a : HQ A u) (b : HQ B v) (c : HQ B s) (e : HQ C t) :
    let T := (A ⊗ C) ⊗ B
    let f : T ⟶ A ⊗ B := lift (fst (A ⊗ C) B ≫ fst A C) (snd (A ⊗ C) B)
    let g : T ⟶ B ⊗ C := lift (snd (A ⊗ C) B) (fst (A ⊗ C) B ≫ snd A C)
    cfd_projection (A ⊗ C) B d I n
      ((cupProductOf T).cup (by omega)
        (homPullback f uv ((cupProductOf (A ⊗ B)).cup huv
          (homPullback (fst A B) u a) (homPullback (snd A B) v b)))
        (homPullback g st ((cupProductOf (B ⊗ C)).cup hst
          (homPullback (fst B C) s c) (homPullback (snd B C) t e)))) = 0 := by
  dsimp only
  let T := (A ⊗ C) ⊗ B
  let f : T ⟶ A ⊗ B := lift (fst (A ⊗ C) B ≫ fst A C) (snd (A ⊗ C) B)
  let g : T ⟶ B ⊗ C := lift (snd (A ⊗ C) B) (fst (A ⊗ C) B ≫ snd A C)
  have hfA : homPullback f u (homPullback (fst A B) u a) =
      homPullback (fst (A ⊗ C) B) u (homPullback (fst A C) u a) := by
    dsimp only [f]
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_fst,
      spec_homPullback_comp, LinearMap.comp_apply]
  have hfB : homPullback f v (homPullback (snd A B) v b) =
      homPullback (snd (A ⊗ C) B) v b := by
    dsimp only [f]
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd]
  have hgB : homPullback g s (homPullback (fst B C) s c) =
      homPullback (snd (A ⊗ C) B) s c := by
    dsimp only [g]
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_fst]
  have hgC : homPullback g t (homPullback (snd B C) t e) =
      homPullback (fst (A ⊗ C) B) t (homPullback (snd A C) t e) := by
    dsimp only [g]
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd,
      spec_homPullback_comp, LinearMap.comp_apply]
  rw [spec_homPullback_cup, spec_homPullback_cup, hfA, hfB, hgB, hgC,
    s4_cup_four_exchange T (cupProductOf T) u v s t (v + s) rfl rfl huv hst (by omega)]
  rw [map_smul,
    ← spec_homPullback_cup (fst (A ⊗ C) B) rfl,
    ← spec_homPullback_cup (snd (A ⊗ C) B) rfl,
    cfd_projection_cross_off (A ⊗ C) B d I n (u + t) (v + s) (by omega) hne,
    smul_zero]

/-- The bilinear kernel obtained by pullback, cup product and integration of the shared factor. -/
def s4_compositeKernel
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (C : Over (Spec ↧ℂ)) [GrpObj C] [IsCommMonObj C]
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c₁ c₂ q : ℕ)
    (h : 2 * c₁ + 2 * c₂ = 2 * q + 2 * d) :
    HQ (A ⊗ B) (2 * c₁) →ₗ[ℚ]
      HQ (B ⊗ C) (2 * c₂) →ₗ[ℚ] HQ (A ⊗ C) (2 * q) :=
  let T := (A ⊗ C) ⊗ B
  let f : T ⟶ A ⊗ B := lift (fst (A ⊗ C) B ≫ fst A C) (snd (A ⊗ C) B)
  let g : T ⟶ B ⊗ C := lift (snd (A ⊗ C) B) (fst (A ⊗ C) B ≫ snd A C)
  (((cupProductOf T).cup h).compl₁₂
    (homPullback f (2 * c₁)) (homPullback g (2 * c₂))).compr₂
      (cfd_projection (A ⊗ C) B d I (2 * q))

/-- The bilinear composition kernel carries algebraic inputs to an algebraic class. -/
theorem s4_compositeKernel_mem
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (C : Over (Spec ↧ℂ)) [GrpObj C] [IsCommMonObj C]
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (d : ℕ) (hdim : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c₁ c₂ q : ℕ)
    (h : 2 * c₁ + 2 * c₂ = 2 * q + 2 * d)
    (ξ : HQ (A ⊗ B) (2 * c₁)) (hξ : ξ ∈ cfd_cycleSpan (A ⊗ B) c₁)
    (κ : HQ (B ⊗ C) (2 * c₂)) (hκ : κ ∈ cfd_cycleSpan (B ⊗ C) c₂) :
    s4_compositeKernel A B C d I c₁ c₂ q h ξ κ ∈ cfd_cycleSpan (A ⊗ C) q := by
  have hh := s4_composite_kernel_algebraic A B C d hdim I c₁ c₂ q (by omega)
    ξ hξ κ hκ
  dsimp only at hh
  rw [CupProduct.castEquiv_cup] at hh
  exact hh

/-- The composite kernel acts as the composite operator on separated classes. -/
theorem s4_corrAction_composite_cross
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (C : Over (Spec ↧ℂ)) [GrpObj C] [IsCommMonObj C]
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (dB dC : ℕ) (hdimB : TopologicalSpace.dim B.left = dB)
    (hdimC : TopologicalSpace.dim C.left = dC)
    (I : HQ B (2 * dB) ≃ₗ[ℚ] ℚ) (J : HQ C (2 * dC) ≃ₗ[ℚ] ℚ)
    (c₁ c₂ qK p qB qA : ℕ)
    (h₁ : 2 * c₁ + 2 * qB = 2 * qA + 2 * dB)
    (h₂ : 2 * c₂ + 2 * p = 2 * qB + 2 * dC)
    (hK : 2 * c₁ + 2 * c₂ = 2 * qK + 2 * dB)
    (u v s t : ℕ) (hξ : u + v = 2 * c₁) (hκ : s + t = 2 * c₂)
    (a : HQ A u) (b : HQ B v) (c : HQ B s) (e : HQ C t)
    (x : HQ C (2 * p)) :
    let ξ := (cupProductOf (A ⊗ B)).cup hξ
      (homPullback (fst A B) u a) (homPullback (snd A B) v b)
    let κ := (cupProductOf (B ⊗ C)).cup hκ
      (homPullback (fst B C) s c) (homPullback (snd B C) t e)
    cfd_corrAction A C dC J qK p qA (by omega)
      (s4_compositeKernel A B C dB I c₁ c₂ qK hK ξ κ) x =
      cfd_corrAction A B dB I c₁ qB qA h₁ ξ
        (cfd_corrAction B C dC J c₂ p qB h₂ κ x) := by
  dsimp only
  by_cases ht : t + 2 * p = 2 * dC
  · have hs : s = 2 * qB := by omega
    subst s
    rw [s4_corrAction_cross_degree B C dC hdimC J c₂ p qB t h₂ ht hκ,
      map_smul]
    by_cases hv : v + 2 * qB = 2 * dB
    · have hu : u = 2 * qA := by omega
      subst u
      have hut : 2 * qA + t = 2 * qK := by omega
      have hk := s4_composite_kernel_cross A B C dB hdimB I
        (2 * qA) v (2 * qB) t (2 * qK) hv hut hξ hκ a b c e
      change s4_compositeKernel A B C dB I c₁ c₂ qK hK _ _ = _ at hk
      rw [hk, s4_corrAction_smul, LinearMap.smul_apply,
        s4_corrAction_cross_degree A C dC hdimC J qK p qA t (by omega) ht hut,
        s4_corrAction_cross_degree A B dB hdimB I c₁ qB qA v h₁ hv hξ]
      exact smul_comm _ _ _
    · have hk := s4_composite_kernel_cross_off A B C dB I
        u v (2 * qB) t (2 * qK) hK hv hξ hκ a b c e
      change s4_compositeKernel A B C dB I c₁ c₂ qK hK _ _ = 0 at hk
      rw [hk, s4_corrAction_cross_off A B dB I c₁ qB qA u v h₁ hξ hv]
      simp only [cfd_corrAction, LinearMap.comp_apply, map_zero, LinearMap.zero_apply,
        smul_zero]
  · rw [s4_corrAction_cross_off B C dC J c₂ p qB s t h₂ hκ ht, map_zero]
    by_cases hv : v + s = 2 * dB
    · have hut : u + t = 2 * qK := by omega
      have hk := s4_composite_kernel_cross A B C dB hdimB I
        u v s t (2 * qK) hv hut hξ hκ a b c e
      change s4_compositeKernel A B C dB I c₁ c₂ qK hK _ _ = _ at hk
      rw [hk, s4_corrAction_smul, LinearMap.smul_apply,
        s4_corrAction_cross_off A C dC J qK p qA u t (by omega) hut ht, smul_zero]
    · have hk := s4_composite_kernel_cross_off A B C dB I
        u v s t (2 * qK) hK hv hξ hκ a b c e
      change s4_compositeKernel A B C dB I c₁ c₂ qK hK _ _ = 0 at hk
      rw [hk]
      simp only [cfd_corrAction, LinearMap.comp_apply, map_zero, LinearMap.zero_apply]

/-- The geometric three-factor kernel realizes composition of correspondence operators. -/
theorem s4_corrAction_composite
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (C : Over (Spec ↧ℂ)) [GrpObj C] [IsCommMonObj C]
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (dB dC : ℕ) (hdimB : TopologicalSpace.dim B.left = dB)
    (hdimC : TopologicalSpace.dim C.left = dC)
    (I : HQ B (2 * dB) ≃ₗ[ℚ] ℚ) (J : HQ C (2 * dC) ≃ₗ[ℚ] ℚ)
    (c₁ c₂ qK p qB qA : ℕ)
    (h₁ : 2 * c₁ + 2 * qB = 2 * qA + 2 * dB)
    (h₂ : 2 * c₂ + 2 * p = 2 * qB + 2 * dC)
    (hK : 2 * c₁ + 2 * c₂ = 2 * qK + 2 * dB)
    (ξ : HQ (A ⊗ B) (2 * c₁)) (κ : HQ (B ⊗ C) (2 * c₂)) :
    cfd_corrAction A C dC J qK p qA (by omega)
      (s4_compositeKernel A B C dB I c₁ c₂ qK hK ξ κ) =
      (cfd_corrAction A B dB I c₁ qB qA h₁ ξ).comp
        (cfd_corrAction B C dC J c₂ p qB h₂ κ) := by
  classical
  let L := (s4_compositeKernel A B C dB I c₁ c₂ qK hK).compr₂
    (s4_corrActionLinear A C dC J qK p qA (by omega))
  let R := (LinearMap.llcomp ℚ (HQ C (2 * p)) (HQ B (2 * qB))
    (HQ A (2 * qA))).compl₁₂
      (s4_corrActionLinear A B dB I c₁ qB qA h₁)
      (s4_corrActionLinear B C dC J c₂ p qB h₂)
  have he : L.comp (cp_kunnethMap A B (2 * c₁)) =
      R.comp (cp_kunnethMap A B (2 * c₁)) := by
    apply DirectSum.linearMap_ext ℚ
    intro k₁
    apply TensorProduct.ext'
    intro a b
    rcases k₁ with ⟨⟨u, v⟩, hk₁⟩
    have hξ : u + v = 2 * c₁ := Finset.HasAntidiagonal.mem_antidiagonal.mp hk₁
    simp only [LinearMap.comp_apply, cp_kunnethMap, DirectSum.toModule_lof,
      TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    let ξ₀ := (cupProductOf (A ⊗ B)).cup hξ
      (homPullback (fst A B) u a) (homPullback (snd A B) v b)
    have he₂ : (L ξ₀).comp (cp_kunnethMap B C (2 * c₂)) =
        (R ξ₀).comp (cp_kunnethMap B C (2 * c₂)) := by
      apply DirectSum.linearMap_ext ℚ
      intro k₂
      apply TensorProduct.ext'
      intro c e
      rcases k₂ with ⟨⟨s, t⟩, hk₂⟩
      have hκ : s + t = 2 * c₂ := Finset.HasAntidiagonal.mem_antidiagonal.mp hk₂
      simp only [LinearMap.comp_apply, cp_kunnethMap, DirectSum.toModule_lof,
        TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
      apply LinearMap.ext
      intro x
      exact s4_corrAction_composite_cross A B C dB dC hdimB hdimC I J
        c₁ c₂ qK p qB qA h₁ h₂ hK u v s t hξ hκ a b c e x
    apply LinearMap.ext
    intro κ₀
    obtain ⟨w, rfl⟩ := (cp_kunneth B C (2 * c₂)).surjective κ₀
    exact LinearMap.congr_fun he₂ w
  change L ξ κ = R ξ κ
  obtain ⟨w, rfl⟩ := (cp_kunneth A B (2 * c₁)).surjective ξ
  exact LinearMap.congr_fun (LinearMap.congr_fun he w) κ

end HodgeLean.Foundations.Program

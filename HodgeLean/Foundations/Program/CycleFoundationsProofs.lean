import HodgeLean.Foundations.Program.CycleFoundationsDefs
import HodgeLean.Foundations.Program.CycleFoundationsFiniteCohomology

/-! Proof obligations for the cycle foundation stage. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] cupProductOf algebraicCycleClassSpan homPullback
namespace HodgeLean.Foundations.Program
theorem cfd_kunneth_one_aux (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)] [∀ i, IsCommMonObj (A i)]
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom] (P : Over (Spec ↧ℂ)) [GrpObj P] [IsCommMonObj P]
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    (π : ∀ i, P ⟶ A i)
    (hπ : Limits.IsLimit (Limits.Fan.mk P π)) :
    Function.Bijective (cfd_oneMap r A P π) := by
  classical
  obtain ⟨hQ⟩ := cfd_product_limit r A
  let f : P ⟶ cfd_product r A := hQ.lift (Limits.Fan.mk P π)
  let g : cfd_product r A ⟶ P :=
    hπ.lift (Limits.Fan.mk (cfd_product r A) (cfd_proj r A))
  have hf (i : Fin r) : f ≫ cfd_proj r A i = π i := hQ.fac _ ⟨i⟩
  have hg (i : Fin r) : g ≫ π i = cfd_proj r A i := hπ.fac _ ⟨i⟩
  have hfg : f ≫ g = 𝟙 P := by
    apply Limits.Fan.IsLimit.hom_ext hπ
    intro i
    change (f ≫ g) ≫ π i = (𝟙 P) ≫ π i
    rw [Category.assoc, hg, hf, Category.id_comp]
  have hgf : g ≫ f = 𝟙 (cfd_product r A) := by
    apply Limits.Fan.IsLimit.hom_ext hQ
    intro i
    change (g ≫ f) ≫ cfd_proj r A i = (𝟙 _) ≫ cfd_proj r A i
    rw [Category.assoc, hf, hg, Category.id_comp]
  have hleft : Function.LeftInverse (homPullback g 1) (homPullback f 1) := by
    intro x
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, hgf,
      spec_homPullback_id, LinearMap.id_apply]
  have hright : Function.RightInverse (homPullback g 1) (homPullback f 1) := by
    intro x
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, hfg,
      spec_homPullback_id, LinearMap.id_apply]
  have he : cfd_oneMap r A P π = (homPullback f 1).comp
      (cfd_oneMap r A (cfd_product r A) (cfd_proj r A)) := by
    ext x
    simp only [cfd_oneMap, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, hf]
  rw [he]
  exact (show Function.Bijective (homPullback f 1) from
    ⟨hleft.injective, hright.surjective⟩).comp (cfd_oneMap_product_bijective r A)

theorem cfd_kunneth_exterior_aux (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)] [∀ i, IsCommMonObj (A i)]
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom] (P : Over (Spec ↧ℂ)) [GrpObj P] [IsCommMonObj P]
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    (π : ∀ i, P ⟶ A i)
    (hπ : Limits.IsLimit (Limits.Fan.mk P π)) (n : ℕ) :
    Function.Bijective ((cupProductOf P).cupWedgeMap n ∘ₗ
      exteriorPower.map n (cfd_oneMap r A P π)) := by
  have hf := cfd_kunneth_one_aux r A P π hπ
  have he : Function.Bijective (exteriorPower.map n (cfd_oneMap r A P π)) :=
    ⟨exteriorPower.map_injective_field hf.injective,
      exteriorPower.map_surjective hf.surjective⟩
  exact (torusCohomology_cupProductOf P).cupWedgeEquiv n |>.bijective.comp he

theorem cfd_projection_cross_aux (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (n : ℕ) (a : HQ A n) (b : HQ B (2 * d)) :
    cfd_projection A B d I n
      ((cupProductOf (A ⊗ B)).cup rfl
        (homPullback (fst A B) n a) (homPullback (snd A B) (2 * d) b)) = I b • a := by
  classical
  let k : Finset.HasAntidiagonal.antidiagonal (n + 2 * d) :=
    ⟨(n, 2 * d), Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  let v : (⨁ p : Finset.HasAntidiagonal.antidiagonal (n + 2 * d),
      HQ A p.1.1 ⊗[ℚ] HQ B p.1.2) := DirectSum.lof ℚ _ _ k (a ⊗ₜ[ℚ] b)
  have hv : cp_kunnethMap A B (n + 2 * d) v =
      (cupProductOf (A ⊗ B)).cup rfl
        (homPullback (fst A B) n a) (homPullback (snd A B) (2 * d) b) := by
    simp [v, cp_kunnethMap, k]
  rw [← hv]
  change (TensorProduct.rid ℚ (HQ A n))
    (TensorProduct.map LinearMap.id I.toLinearMap
      (DirectSum.component ℚ _ _ k
        ((LinearEquiv.ofBijective (cp_kunnethMap A B (n + 2 * d))
          (cp_kunneth A B (n + 2 * d))).symm
          ((LinearEquiv.ofBijective (cp_kunnethMap A B (n + 2 * d))
            (cp_kunneth A B (n + 2 * d))) v)))) = _
  rw [LinearEquiv.symm_apply_apply]
  dsimp only [v]
  rw [DirectSum.component.lof_self]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul]

theorem cfd_projection_cross_off (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (n u v : ℕ)
    (h : u + v = n + 2 * d) (hv : v ≠ 2 * d) (a : HQ A u) (b : HQ B v) :
    cfd_projection A B d I n ((cupProductOf (A ⊗ B)).cup h
      (homPullback (fst A B) u a) (homPullback (snd A B) v b)) = 0 := by
  classical
  let k : Finset.HasAntidiagonal.antidiagonal (n + 2 * d) :=
    ⟨(u, v), Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩
  let z : (⨁ p : Finset.HasAntidiagonal.antidiagonal (n + 2 * d),
      HQ A p.1.1 ⊗[ℚ] HQ B p.1.2) := DirectSum.lof ℚ _ _ k (a ⊗ₜ[ℚ] b)
  have hz : cp_kunnethMap A B (n + 2 * d) z =
      (cupProductOf (A ⊗ B)).cup h
        (homPullback (fst A B) u a) (homPullback (snd A B) v b) := by
    simp only [z, cp_kunnethMap, DirectSum.toModule_lof, TensorProduct.lift.tmul,
      LinearMap.compl₁₂_apply]
    rfl
  rw [← hz]
  let t : Finset.HasAntidiagonal.antidiagonal (n + 2 * d) :=
    ⟨(n, 2 * d), Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  have hkt : k ≠ t := fun he => hv (congrArg (fun p => p.1.2) he)
  change (TensorProduct.rid ℚ (HQ A n))
    (TensorProduct.map LinearMap.id I.toLinearMap
      (DirectSum.component ℚ _ _ t
        ((LinearEquiv.ofBijective (cp_kunnethMap A B (n + 2 * d))
          (cp_kunneth A B (n + 2 * d))).symm
          ((LinearEquiv.ofBijective (cp_kunnethMap A B (n + 2 * d))
            (cp_kunneth A B (n + 2 * d))) z)))) = 0
  rw [LinearEquiv.symm_apply_apply]
  simp only [z, DirectSum.component.of, dif_neg hkt, map_zero]

theorem cfd_projection_formula_aux (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (i j : ℕ) (a : HQ A i) (b : HQ (A ⊗ B) (j + 2 * d)) :
    cfd_projection A B d I (i + j)
      ((cupProductOf (A ⊗ B)).cup (Nat.add_assoc i j (2 * d)).symm
        (homPullback (fst A B) i a) b) =
      (cupProductOf A).cup rfl a (cfd_projection A B d I j b) := by
  classical
  let L := (cfd_projection A B d I (i + j)).comp
    ((cupProductOf (A ⊗ B)).cup (Nat.add_assoc i j (2 * d)).symm
      (homPullback (fst A B) i a))
  let R := ((cupProductOf A).cup rfl a).comp (cfd_projection A B d I j)
  have he : L.comp (cp_kunnethMap A B (j + 2 * d)) =
      R.comp (cp_kunnethMap A B (j + 2 * d)) := by
    apply DirectSum.linearMap_ext ℚ
    intro k
    apply TensorProduct.ext'
    intro u v
    rcases k with ⟨⟨s, t⟩, hk⟩
    have hst : s + t = j + 2 * d := Finset.HasAntidiagonal.mem_antidiagonal.mp hk
    simp only [LinearMap.comp_apply, cp_kunnethMap, DirectSum.toModule_lof,
      TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    change cfd_projection A B d I (i + j)
      ((cupProductOf (A ⊗ B)).cup (Nat.add_assoc i j (2 * d)).symm
        (homPullback (fst A B) i a)
        ((cupProductOf (A ⊗ B)).cup hst
          (homPullback (fst A B) s u) (homPullback (snd A B) t v))) =
      (cupProductOf A).cup rfl a
        (cfd_projection A B d I j ((cupProductOf (A ⊗ B)).cup hst
          (homPullback (fst A B) s u) (homPullback (snd A B) t v)))
    rw [← (cupProductOf (A ⊗ B)).assoc rfl hst (by omega)
      (Nat.add_assoc i j (2 * d)).symm,
      ← spec_homPullback_cup (fst A B) rfl]
    by_cases ht : t = 2 * d
    · subst t
      have hs : s = j := by omega
      subst s
      rw [cfd_projection_cross_aux A B d hB I (i + j),
        cfd_projection_cross_aux A B d hB I j]
      exact ((cupProductOf A).cup rfl a).map_smul (I v) u |>.symm
    · rw [cfd_projection_cross_off A B d I (i + j) (i + s) t (by omega) ht,
        cfd_projection_cross_off A B d I j s t hst ht, map_zero]
  obtain ⟨z, hz⟩ := (cp_kunneth A B (j + 2 * d)).surjective b
  exact hz ▸ LinearMap.congr_fun he z

end HodgeLean.Foundations.Program

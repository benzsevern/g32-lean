import HodgeLean.Foundations.Program.CompensationCubicGrpObj
import HodgeLean.Adapters.AbelianEndomorphisms2
import HodgeLean.Foundations.Program.CompensationProductDefs
import HodgeLean.Foundations.DirectSumInvariants
import HodgeLean.Foundations.Program.CompensationProductLinear
import HodgeLean.Foundations.Program.CompensationProductPolarisation
import HodgeLean.Foundations.Program.CompensationProductWeilDet
import HodgeLean.Foundations.Program.CompensationCMDet

/-! # Proof obligations for the compensation product, stages C1–C4

Proofs of the statements of `CompensationProduct.lean`.
HC no distance; AV milestone no distance.
-/

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations.HermitianForm

namespace HodgeLean.Foundations.Program

/-- Reindex the finite antidiagonal by its defining degree equality.
Source: Mathlib `Finset.HasAntidiagonal.mem_antidiagonal`. -/
private def cp_antidiagonalEquiv (n : ℕ) :
    Finset.HasAntidiagonal.antidiagonal n ≃ {p : ℕ × ℕ // p.1 + p.2 = n} where
  toFun p := ⟨p.1, Finset.HasAntidiagonal.mem_antidiagonal.mp p.2⟩
  invFun p := ⟨p.1, Finset.HasAntidiagonal.mem_antidiagonal.mpr p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem cp_antidiagonal_reindex_lof {K U V : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (n : ℕ) (p : Finset.HasAntidiagonal.antidiagonal n)
    (v : ⋀[K]^p.1.1 U ⊗[K] ⋀[K]^p.1.2 V) :
    DirectSum.lequivCongrLeft K (M := fun p : Finset.HasAntidiagonal.antidiagonal n =>
      ⋀[K]^p.1.1 U ⊗[K] ⋀[K]^p.1.2 V) (cp_antidiagonalEquiv n)
      (DirectSum.lof K _ _ p v) =
        DirectSum.lof K _ _ (cp_antidiagonalEquiv n p) v := by
  classical
  exact DirectSum.lequivCongrLeft_lof K
    (M := fun p : Finset.HasAntidiagonal.antidiagonal n =>
      ⋀[K]^p.1.1 U ⊗[K] ⋀[K]^p.1.2 V)
    (e := cp_antidiagonalEquiv n) (i := p) (k := cp_antidiagonalEquiv n p) rfl v v rfl

private theorem cp_split_submodule_rank {K U V Z : Type*} [Field K]
    [AddCommGroup U] [Module K U] [Module.Finite K U]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup Z] [Module K Z]
    (f : U →ₗ[K] Z) (g : V →ₗ[K] Z) (p : Z →ₗ[K] U) (q : Z →ₗ[K] V)
    (hpf : ∀ x, p (f x) = x) (hpg : ∀ y, p (g y) = 0)
    (hqf : ∀ x, q (f x) = 0) (hqg : ∀ y, q (g y) = y)
    (hsplit : ∀ z, f (p z) + g (q z) = z)
    (P : Submodule K U) (Q : Submodule K V) (R : Submodule K Z)
    (hf : ∀ x ∈ P, f x ∈ R) (hg : ∀ y ∈ Q, g y ∈ R)
    (hp : ∀ z ∈ R, p z ∈ P) (hq : ∀ z ∈ R, q z ∈ Q) :
    Module.finrank K R = Module.finrank K P + Module.finrank K Q := by
  let F : P × Q →ₗ[K] R :=
    { toFun := fun x => ⟨f x.1 + g x.2, R.add_mem (hf _ x.1.2) (hg _ x.2.2)⟩
      map_add' := by intro x y; ext; simp only [Prod.fst_add, Prod.snd_add,
        Submodule.coe_add, map_add]; abel
      map_smul' := by intro c x; ext; simp only [Prod.smul_fst, Prod.smul_snd,
        SetLike.val_smul, map_smul, smul_add, RingHom.id_apply] }
  let G : R → P × Q := fun z => (⟨p z, hp _ z.2⟩, ⟨q z, hq _ z.2⟩)
  have hl : Function.LeftInverse G F := by
    intro x
    apply Prod.ext <;> apply Subtype.ext
    · exact (map_add p _ _).trans (by rw [hpf, hpg, add_zero])
    · exact (map_add q _ _).trans (by rw [hqf, hqg, zero_add])
  have hr : Function.RightInverse G F := by
    intro z; apply Subtype.ext; exact hsplit z
  have he := (LinearEquiv.ofBijective F ⟨hl.injective, hr.surjective⟩).finrank_eq
  rw [Module.finrank_prod] at he
  exact he.symm

/-! ### C1 and C2 -/

section Product

variable (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom] [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cp_kunneth_H1_aux :
    Function.Bijective (fun p : HQ A 1 × HQ Y 1 =>
      homPullback (fst A Y) 1 p.1 + homPullback (snd A Y) 1 p.2) := by
  let iA : A ⟶ A ⊗ Y := lift (𝟙 A) 1
  let iY : Y ⟶ A ⊗ Y := lift 1 (𝟙 Y)
  let f : HQ A 1 × HQ Y 1 → HQ (A ⊗ Y) 1 := fun p =>
    homPullback (fst A Y) 1 p.1 + homPullback (snd A Y) 1 p.2
  let g : HQ (A ⊗ Y) 1 → HQ A 1 × HQ Y 1 := fun x =>
    (homPullback iA 1 x, homPullback iY 1 x)
  have hleft : Function.LeftInverse g f := by
    intro p
    apply Prod.ext <;>
      simp only [g, f, map_add, ← LinearMap.comp_apply, ← spec_homPullback_comp,
        iA, iY, lift_fst, lift_snd, spec_homPullback_id, spec_homPullback_one,
        LinearMap.id_apply, LinearMap.zero_apply, add_zero, zero_add]
  have hsplit : fst A Y ≫ iA * (snd A Y ≫ iY) = 𝟙 (A ⊗ Y) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.mul_comp, iA, iY, MonObj.comp_one]
  have hright : Function.RightInverse g f := by
    intro x
    change homPullback (fst A Y) 1 (homPullback iA 1 x) +
      homPullback (snd A Y) 1 (homPullback iY 1 x) = x
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← spec_homPullback_comp,
      ← spec_homPullback_comp, ← LinearMap.add_apply, ← spec_homPullback_mul,
      hsplit, spec_homPullback_id, LinearMap.id_apply]
  exact ⟨hleft.injective, hright.surjective⟩

/-- The degree-one Künneth equivalence given by the two projection pullbacks.
Source: `cp_kunneth_H1_aux`. -/
def cp_H1Equiv : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1 :=
  LinearEquiv.ofBijective ((homPullback (fst A Y) 1).coprod (homPullback (snd A Y) 1))
    (cp_kunneth_H1_aux A Y)

/-- The inverse Künneth equivalence is restriction to the two factors.
Source: `spec_homPullback_comp`, the two inclusion–projection identities. -/
theorem cp_H1Equiv_symm (x : HQ (A ⊗ Y) 1) :
    (cp_H1Equiv A Y).symm x =
      (homPullback (lift (𝟙 A) (1 : A ⟶ Y)) 1 x,
        homPullback (lift (1 : Y ⟶ A) (𝟙 Y)) 1 x) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (cp_H1Equiv A Y).surjective x
  rw [LinearEquiv.symm_apply_apply]
  apply Prod.ext <;>
    change _ = homPullback _ 1 (homPullback (fst A Y) 1 a + homPullback (snd A Y) 1 b) <;>
    simp only [map_add, ← LinearMap.comp_apply, ← spec_homPullback_comp,
      lift_fst, lift_snd, spec_homPullback_id, spec_homPullback_one,
      LinearMap.id_apply, LinearMap.zero_apply, add_zero, zero_add]

theorem cp_product_dim_aux :
    TopologicalSpace.dim (A ⊗ Y).left = TopologicalSpace.dim A.left + TopologicalSpace.dim Y.left := by
  letI := (finiteBetti_abelian A).finite 1
  letI := (finiteBetti_abelian Y).finite 1
  let f := (homPullback (fst A Y) 1).coprod (homPullback (snd A Y) 1)
  have hf : Function.Bijective f := cp_kunneth_H1_aux A Y
  have hdim := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [Module.finrank_prod, (torusCohomology_cupProductOf A).finrank_eq,
    (torusCohomology_cupProductOf Y).finrank_eq,
    (torusCohomology_cupProductOf (A ⊗ Y)).finrank_eq] at hdim
  omega

/-- The polarization vector of a product is the sum of the two pulled-back vectors.
Source: `spec_homPullback_cupWedgeMap`, linearity of the cup comparison. -/
theorem cp_product_polarizationVec (polA : HQ A 2) (polY : HQ Y 2) :
    polarizationVec (torusCohomology_cupProductOf (A ⊗ Y)) (cp_productPol A Y polA polY) =
      exteriorPower.map 2 (homPullback (fst A Y) 1)
          (polarizationVec (torusCohomology_cupProductOf A) polA) +
        exteriorPower.map 2 (homPullback (snd A Y) 1)
          (polarizationVec (torusCohomology_cupProductOf Y) polY) := by
  apply ((torusCohomology_cupProductOf (A ⊗ Y)).cupWedgeEquiv 2).injective
  rw [TorusCohomology.cupWedgeEquiv_apply, cupWedgeMap_polarizationVec, map_add]
  have hA := LinearMap.congr_fun (spec_homPullback_cupWedgeMap (fst A Y) 2)
    (polarizationVec (torusCohomology_cupProductOf A) polA)
  have hY := LinearMap.congr_fun (spec_homPullback_cupWedgeMap (snd A Y) 2)
    (polarizationVec (torusCohomology_cupProductOf Y) polY)
  simp only [LinearMap.comp_apply, cupWedgeMap_polarizationVec] at hA hY
  change homPullback (fst A Y) 2 polA + homPullback (snd A Y) 2 polY = _
  rw [TorusCohomology.cupWedgeEquiv_apply, TorusCohomology.cupWedgeEquiv_apply, ← hA, ← hY]

/-- The product class is nondegenerate when both factor classes are nondegenerate.
Source: `cp_sumVec_nondegenerate`, `cp_map_nondegenerate`, degree-one Künneth. -/
theorem cp_product_pol_nondegenerate (polA : HQ A 2) (polY : HQ Y 2)
    (hA : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) polA))
    (hY : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf Y) polY)) :
    IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (A ⊗ Y))
      (cp_productPol A Y polA polY)) := by
  letI := (finiteBetti_abelian A).finite 1
  letI := (finiteBetti_abelian Y).finite 1
  letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
  let f := (homPullback (fst A Y) 1).coprod (homPullback (snd A Y) 1)
  let e := LinearEquiv.ofBijective f (cp_kunneth_H1_aux A Y)
  have hinl : e.toLinearMap ∘ₗ LinearMap.inl ℚ (HQ A 1) (HQ Y 1) = homPullback (fst A Y) 1 := by
    ext x
    change homPullback (fst A Y) 1 x + homPullback (snd A Y) 1 0 = homPullback (fst A Y) 1 x
    rw [map_zero, add_zero]
  have hinr : e.toLinearMap ∘ₗ LinearMap.inr ℚ (HQ A 1) (HQ Y 1) = homPullback (snd A Y) 1 := by
    ext x
    change homPullback (fst A Y) 1 0 + homPullback (snd A Y) 1 x = homPullback (snd A Y) 1 x
    rw [map_zero, zero_add]
  have h := cp_map_nondegenerate e (cp_sumVec_nondegenerate hA hY)
  rw [cp_sumVec, map_add] at h
  simp only [cp_exterior_map_map] at h
  rw [hinl, hinr, ← cp_product_polarizationVec A Y] at h
  exact h

/-- Künneth transports the direct sum of the two polarization vectors to the product vector.
Source: `cp_product_polarizationVec`, functoriality of exterior powers. -/
theorem cp_H1Equiv_map_sumVec (polA : HQ A 2) (polY : HQ Y 2) :
    exteriorPower.map 2 (cp_H1Equiv A Y).toLinearMap
      (cp_sumVec (polarizationVec (torusCohomology_cupProductOf A) polA)
        (polarizationVec (torusCohomology_cupProductOf Y) polY)) =
      polarizationVec (torusCohomology_cupProductOf (A ⊗ Y)) (cp_productPol A Y polA polY) := by
  have hinl : (cp_H1Equiv A Y).toLinearMap ∘ₗ LinearMap.inl ℚ (HQ A 1) (HQ Y 1) =
      homPullback (fst A Y) 1 := by
    ext x
    change homPullback (fst A Y) 1 x + homPullback (snd A Y) 1 0 = _
    rw [map_zero, add_zero]
  have hinr : (cp_H1Equiv A Y).toLinearMap ∘ₗ LinearMap.inr ℚ (HQ A 1) (HQ Y 1) =
      homPullback (snd A Y) 1 := by
    ext x
    change homPullback (fst A Y) 1 0 + homPullback (snd A Y) 1 x = _
    rw [map_zero, zero_add]
  rw [cp_sumVec, map_add]
  simp only [cp_exterior_map_map]
  rw [hinl, hinr, ← cp_product_polarizationVec A Y]

/-- The product dual form is the sum of its restrictions along the two inclusions.
Source: `cp_dualForm_map_of_eq`, `cp_dualForm_sumVec`. -/
theorem cp_product_dualForm (polA : HQ A 2) (polY : HQ Y 2)
    (hA : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) polA))
    (hY : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf Y) polY))
    (hP : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (A ⊗ Y))
      (cp_productPol A Y polA polY))) (x y : HQ (A ⊗ Y) 1) :
    dualForm hP x y =
      dualForm hA (homPullback (lift (𝟙 A) (1 : A ⟶ Y)) 1 x)
        (homPullback (lift (𝟙 A) (1 : A ⟶ Y)) 1 y) +
      dualForm hY (homPullback (lift (1 : Y ⟶ A) (𝟙 Y)) 1 x)
        (homPullback (lift (1 : Y ⟶ A) (𝟙 Y)) 1 y) := by
  letI := (finiteBetti_abelian A).finite 1
  letI := (finiteBetti_abelian Y).finite 1
  letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
  have h := cp_dualForm_map_of_eq (cp_H1Equiv A Y) (cp_sumVec_nondegenerate hA hY) hP
    (cp_H1Equiv_map_sumVec A Y polA polY) ((cp_H1Equiv A Y).symm x) ((cp_H1Equiv A Y).symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, cp_dualForm_sumVec,
    cp_H1Equiv_symm, cp_H1Equiv_symm] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem cp_kunneth_aux (n : ℕ) : Function.Bijective (cp_kunnethMap A Y n) := by
  classical
  let TA := torusCohomology_cupProductOf A
  let TY := torusCohomology_cupProductOf Y
  let TP := torusCohomology_cupProductOf (A ⊗ Y)
  let f := (homPullback (fst A Y) 1).coprod (homPullback (snd A Y) 1)
  have hf : Function.Bijective f := cp_kunneth_H1_aux A Y
  let I := cp_antidiagonalEquiv n
  let e₀ := DirectSum.congrLinearEquiv fun p : Finset.HasAntidiagonal.antidiagonal n =>
    TensorProduct.congr (TA.cupWedgeEquiv p.1.1).symm (TY.cupWedgeEquiv p.1.2).symm
  let e₁ : (⨁ p : Finset.HasAntidiagonal.antidiagonal n,
      ⋀[ℚ]^p.1.1 (HQ A 1) ⊗[ℚ] ⋀[ℚ]^p.1.2 (HQ Y 1)) ≃ₗ[ℚ]
      (⨁ p : {q : ℕ × ℕ // q.1 + q.2 = n},
        ⋀[ℚ]^p.1.1 (HQ A 1) ⊗[ℚ] ⋀[ℚ]^p.1.2 (HQ Y 1)) :=
    DirectSum.lequivCongrLeft ℚ (M := fun p : Finset.HasAntidiagonal.antidiagonal n =>
      ⋀[ℚ]^p.1.1 (HQ A 1) ⊗[ℚ] ⋀[ℚ]^p.1.2 (HQ Y 1)) I
  let e₂ := LinearEquiv.ofBijective
    (exteriorProdDegree (K := ℚ) (S₁ := HQ A 1) (S₂ := HQ Y 1) n)
    (spec_a3a_exteriorProdDegree_bijective n)
  let e₃ := LinearEquiv.ofBijective (exteriorPower.map n f)
    ⟨exteriorPower.map_injective_field hf.injective, exteriorPower.map_surjective hf.surjective⟩
  let e := e₀ ≪≫ₗ e₁ ≪≫ₗ e₂ ≪≫ₗ e₃ ≪≫ₗ TP.cupWedgeEquiv n
  have he : e.toLinearMap = cp_kunnethMap A Y n := by
    apply DirectSum.linearMap_ext ℚ
    intro p
    apply TensorProduct.ext'
    intro a b
    have hreindex (v : ⋀[ℚ]^p.1.1 (HQ A 1) ⊗[ℚ] ⋀[ℚ]^p.1.2 (HQ Y 1)) :
        e₁ (DirectSum.lof ℚ _ _ p v) = DirectSum.lof ℚ _ _ (I p) v := by
      exact cp_antidiagonal_reindex_lof n p v
    change TP.cupWedgeEquiv n (exteriorPower.map n f
      (exteriorProdDegree n (e₁ (e₀ (DirectSum.lof ℚ _ _ p (a ⊗ₜ[ℚ] b)))))) =
        cp_kunnethMap A Y n (DirectSum.lof ℚ _ _ p (a ⊗ₜ[ℚ] b))
    have he₀ : e₀ (DirectSum.lof ℚ _ _ p (a ⊗ₜ[ℚ] b)) =
        DirectSum.lof ℚ _ _ p
          ((TA.cupWedgeEquiv p.1.1).symm a ⊗ₜ[ℚ] (TY.cupWedgeEquiv p.1.2).symm b) := by
      change DirectSum.lmap (fun q : Finset.HasAntidiagonal.antidiagonal n =>
        (TensorProduct.congr (TA.cupWedgeEquiv q.1.1).symm
          (TY.cupWedgeEquiv q.1.2).symm).toLinearMap)
        (DirectSum.lof ℚ _ _ p (a ⊗ₜ[ℚ] b)) = _
      rw [DirectSum.lmap_lof]
      simp only [LinearEquiv.coe_coe, TensorProduct.congr_tmul]
    rw [he₀, hreindex]
    dsimp only [I, cp_antidiagonalEquiv, Equiv.symm]
    simp only [exteriorProdDegree, DirectSum.toModule_lof, LinearMap.comp_apply,
      cp_kunnethMap, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    rcases p with ⟨⟨i, j⟩, hp⟩
    have hij : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    subst n
    simp only [I, cp_antidiagonalEquiv, Equiv.coe_fn_mk, LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply, exteriorProdMul, TensorProduct.lift.tmul,
      LinearMap.comp_apply, LinearMap.compl₂_apply]
    change TP.cupWedgeEquiv (i + j) (exteriorPower.map (i + j) f
      (exteriorPower.wedge ℚ (HQ A 1 × HQ Y 1) i j
        (exteriorPower.map i (LinearMap.inl ℚ (HQ A 1) (HQ Y 1)) ((TA.cupWedgeEquiv i).symm a))
        (exteriorPower.map j (LinearMap.inr ℚ (HQ A 1) (HQ Y 1)) ((TY.cupWedgeEquiv j).symm b)))) =
      (cupProductOf (A ⊗ Y)).cup rfl (homPullback (fst A Y) i a) (homPullback (snd A Y) j b)
    have hwedge : exteriorPower.map (i + j) f
        (exteriorPower.wedge ℚ (HQ A 1 × HQ Y 1) i j
          (exteriorPower.map i (LinearMap.inl ℚ (HQ A 1) (HQ Y 1)) ((TA.cupWedgeEquiv i).symm a))
          (exteriorPower.map j (LinearMap.inr ℚ (HQ A 1) (HQ Y 1)) ((TY.cupWedgeEquiv j).symm b))) =
        exteriorPower.wedge ℚ (HQ (A ⊗ Y) 1) i j
          (exteriorPower.map i f (exteriorPower.map i (LinearMap.inl ℚ (HQ A 1) (HQ Y 1))
            ((TA.cupWedgeEquiv i).symm a)))
          (exteriorPower.map j f (exteriorPower.map j (LinearMap.inr ℚ (HQ A 1) (HQ Y 1))
            ((TY.cupWedgeEquiv j).symm b))) := by
      apply Subtype.ext
      simp only [exteriorPower.coe_map, coe_wedge, map_mul]
    rw [hwedge]
    simp only [cp_exterior_map_map]
    have hinl : f ∘ₗ LinearMap.inl ℚ (HQ A 1) (HQ Y 1) = homPullback (fst A Y) 1 := by
      ext x; simp only [f, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.coprod_apply, map_zero, add_zero]
    have hinr : f ∘ₗ LinearMap.inr ℚ (HQ A 1) (HQ Y 1) = homPullback (snd A Y) 1 := by
      ext x; simp only [f, LinearMap.comp_apply, LinearMap.inr_apply,
        LinearMap.coprod_apply, map_zero, zero_add]
    rw [hinl, hinr, TorusCohomology.cupWedgeEquiv_apply, CupProduct.cupWedgeMap_wedge]
    have hA := LinearMap.congr_fun (spec_homPullback_cupWedgeMap (fst A Y) i)
      ((TA.cupWedgeEquiv i).symm a)
    have hY := LinearMap.congr_fun (spec_homPullback_cupWedgeMap (snd A Y) j)
      ((TY.cupWedgeEquiv j).symm b)
    simp only [LinearMap.comp_apply] at hA hY
    rw [← hA, ← hY]
    change (cupProductOf (A ⊗ Y)).cup rfl
      (homPullback (fst A Y) i ((TA.cupWedgeEquiv i) ((TA.cupWedgeEquiv i).symm a)))
      (homPullback (snd A Y) j ((TY.cupWedgeEquiv j) ((TY.cupWedgeEquiv j).symm b))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [← he]
  exact e.bijective

end Product

/-! ### C3 -/

private theorem cp_zeta_ne_zero : cp_zeta ≠ 0 := by
  intro h
  have hh := cp_zeta_cube
  rw [h] at hh
  norm_num at hh

private theorem cp_scaled_slope (x₁ x₂ y₁ y₂ : ℂ) :
    cp_W.toAffine.slope (cp_zeta * x₁) (cp_zeta * x₂) y₁ y₂ =
      cp_zeta ^ 2 * cp_W.toAffine.slope x₁ x₂ y₁ y₂ := by
  classical
  by_cases hx : x₁ = x₂
  · subst x₂
    simp only [WeierstrassCurve.Affine.slope, ite_true,
      WeierstrassCurve.Affine.negY, cp_W, zero_mul, sub_zero]
    split_ifs <;> ring
  · have hz := cp_zeta_ne_zero
    rw [WeierstrassCurve.Affine.slope_of_X_ne (fun hh => hx (mul_left_cancel₀ hz hh)),
      WeierstrassCurve.Affine.slope_of_X_ne hx]
    have hd : cp_zeta * x₁ - cp_zeta * x₂ ≠ 0 := by
      rw [← mul_sub]; exact mul_ne_zero hz (sub_ne_zero.mpr hx)
    field_simp
    linear_combination -(y₁ - y₂) * cp_zeta_cube

theorem cp_cubicAut_add_aux (P Q : cp_W.toAffine.Point) :
    cp_cubicAut (P + Q) = cp_cubicAut P + cp_cubicAut Q := by
  classical
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      have hneg (x y : ℂ) : cp_W.toAffine.negY x y = -y := by
        simp only [WeierstrassCurve.Affine.negY, cp_W, zero_mul, sub_zero]
      have hvertical :
          (cp_zeta * x₁ = cp_zeta * x₂ ∧
            y₁ = cp_W.toAffine.negY (cp_zeta * x₂) y₂) ↔
          (x₁ = x₂ ∧ y₁ = cp_W.toAffine.negY x₂ y₂) := by
        rw [hneg, hneg, mul_right_inj' cp_zeta_ne_zero]
      by_cases hv : x₁ = x₂ ∧ y₁ = cp_W.toAffine.negY x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hv.1 hv.2]
        exact (WeierstrassCurve.Affine.Point.add_of_Y_eq
          (hvertical.mpr hv).1 (hvertical.mpr hv).2).symm
      · simp only [cp_cubicAut, WeierstrassCurve.Affine.Point.add_some hv,
          WeierstrassCurve.Affine.Point.add_some (hvertical.not.mpr hv),
          WeierstrassCurve.Affine.Point.some.injEq]
        simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
          WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
        rw [cp_scaled_slope]
        generalize cp_W.toAffine.slope x₁ x₂ y₁ y₂ = l
        simp only [cp_W]
        constructor
        · linear_combination -(cp_zeta * l ^ 2) * cp_zeta_cube
        · linear_combination
            (l ^ 3 * (cp_zeta ^ 3 + 1) -
              (2 * x₁ + x₂) * l) * cp_zeta_cube

theorem cp_cubicAut_relation_aux (P : cp_W.toAffine.Point) :
    P + cp_cubicAut P + cp_cubicAut (cp_cubicAut P) = 0 := by
  classical
  have hz : cp_zeta ≠ 1 := by
    intro h
    have hh := cp_zeta_sq_add
    rw [h] at hh
    norm_num at hh
  have hxzero (x : ℂ) (h : x = cp_zeta * x) : x = 0 := by
    have hh : (cp_zeta - 1) * x = 0 := by linear_combination -h
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hz)
  cases P with
  | zero => rfl
  | some x y h =>
    have hxy : ¬(x = cp_zeta * x ∧ y = cp_W.toAffine.negY (cp_zeta * x) y) := by
      rintro ⟨hx, hy⟩
      have hx0 := hxzero x hx
      have hy0 : y = 0 := by
        simp only [WeierstrassCurve.Affine.negY, cp_W, zero_mul, sub_zero] at hy
        linear_combination hy / 2
      have heq := h.1
      rw [WeierstrassCurve.Affine.equation_iff] at heq
      norm_num [cp_W, hx0, hy0] at heq
    have hs : cp_W.toAffine.slope x (cp_zeta * x) y y = 0 := by
      by_cases hx : x = cp_zeta * x
      · have hx0 := hxzero x hx
        rw [WeierstrassCurve.Affine.slope_of_Y_ne hx (fun hy => hxy ⟨hx, hy⟩), hx0]
        simp only [cp_W, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add,
          add_zero, sub_zero, zero_mul, zero_div]
      · rw [WeierstrassCurve.Affine.slope_of_X_ne hx, sub_self, zero_div]
    have hsum : WeierstrassCurve.Affine.Point.some x y h +
        cp_cubicAut (.some x y h) = -cp_cubicAut (cp_cubicAut (.some x y h)) := by
      simp only [cp_cubicAut, WeierstrassCurve.Affine.Point.add_some hxy,
        WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq]
      simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
      rw [hs]
      simp only [cp_W]
      constructor
      · linear_combination -x * cp_zeta_sq_add
      · ring
    rw [hsum, neg_add_cancel]

theorem cp_exists_cm_curve_aux :
    ∃ (E : Over (Spec ↧ℂ)) (_ : GrpObj E) (_ : IsIntegral E.left) (ρ : E ⟶ E),
      Smooth E.hom ∧ IsProjective E.hom ∧ TopologicalSpace.dim E.left = 1 ∧ IsMonHom ρ ∧
        𝟙 E * ρ * (ρ ≫ ρ) = 1 ∧
        ∃ e : ComplexPoint E ≃ cp_W.toAffine.Point,
          (∀ P Q : ComplexPoint E, e (P * Q) = e P + e Q) ∧
            ∀ P : ComplexPoint E, e (P ≫ ρ) = cp_cubicAut (e P) := by
  obtain ⟨e, he⟩ := CompensationCubic.exists_isCubicPointEquiv_aux
  obtain ⟨m, hm⟩ := CompensationCubic.exists_add_morphism_aux e he
  obtain ⟨i, hi⟩ := CompensationCubic.exists_neg_morphism_aux e he
  obtain ⟨G, hG0, hGmul, hGinv⟩ :=
    CompensationCubic.exists_grpObj_aux e (he.1 _ rfl) m hm i hi
  letI := G
  obtain ⟨ρ, hρ⟩ := CompensationCubic.exists_rho_morphism_aux e he
  unfold CompensationCubic.W at *
  have emul (P Q : ComplexPoint CompensationCubic.E) : e (P * Q) = e P + e Q := by
    rw [Hom.mul_def, show μ[CompensationCubic.E] = m from hGmul, hm,
      Equiv.apply_symm_apply]
  have eone : e (1 : ComplexPoint CompensationCubic.E) = 0 := by
    have h := emul 1 1
    rw [one_mul] at h
    exact (add_eq_left.mp h.symm)
  have hmon : IsMonHom ρ := by
    apply (spec_isMonHom_iff_pointMap_mul CompensationCubic.E ρ).2
    intro P Q
    apply e.injective
    change e ((P * Q) ≫ ρ) = e ((P ≫ ρ) * (Q ≫ ρ))
    rw [emul, hρ, hρ, hρ, emul]
    exact cp_cubicAut_add_aux (e P) (e Q)
  have hrel : 𝟙 CompensationCubic.E * ρ * (ρ ≫ ρ) = 1 := by
    apply Curves.complexPoint_hom_ext_aux
    intro P
    apply e.injective
    simp only [MonObj.comp_mul, Category.comp_id, ← Category.assoc, MonObj.comp_one]
    rw [emul, emul, hρ, hρ, hρ, eone]
    exact cp_cubicAut_relation_aux (e P)
  exact ⟨CompensationCubic.E, G, inferInstance, ρ, inferInstance, inferInstance,
    CompensationCubic.E_dim, hmon, hrel, e, emul, hρ⟩

theorem cp_weilOperator_sq_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (σ : X ⟶ X) (hσ : 𝟙 X * σ * (σ ≫ σ) = 1) :
    cp_weilOperator X σ ∘ₗ cp_weilOperator X σ = (-3 : ℚ) • LinearMap.id := by
  have h := congrArg (fun f : X ⟶ X => homPullback f 1) hσ
  rw [spec_homPullback_mul, spec_homPullback_mul, spec_homPullback_id,
    spec_homPullback_comp, spec_homPullback_one] at h
  ext x
  have hx := congrArg (fun f : Module.End ℚ (HQ X 1) => f x) h
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.zero_apply] at hx
  simp only [cp_weilOperator, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.smul_apply, map_add, map_smul]
  calc
    x + (2 : ℚ) • homPullback σ 1 x +
        (2 : ℚ) • (homPullback σ 1 x + (2 : ℚ) • homPullback σ 1 (homPullback σ 1 x)) =
      (-3 : ℚ) • x + (4 : ℚ) •
        (x + homPullback σ 1 x + homPullback σ 1 (homPullback σ 1 x)) := by module
    _ = (-3 : ℚ) • x := by rw [hx, smul_zero, add_zero]

theorem cp_conjAut_relation_aux (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] (ρ : E ⟶ E)
    [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) :
    𝟙 (E ⊗ E) * cp_conjAut E ρ * (cp_conjAut E ρ ≫ cp_conjAut E ρ) = 1 := by
  have hcomp := congrArg (fun f : E ⟶ E => ρ ≫ f) hρ
  simp only [MonObj.comp_mul, Category.comp_id, MonObj.comp_one] at hcomp
  have hcube : ρ ≫ ρ ≫ ρ = 𝟙 E := by
    apply mul_left_cancel (a := ρ * (ρ ≫ ρ))
    calc
      ρ * (ρ ≫ ρ) * (ρ ≫ ρ ≫ ρ) = 1 := hcomp
      _ = ρ * (ρ ≫ ρ) * 𝟙 E := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hρ.symm
  have hfour : ρ ≫ ρ ≫ ρ ≫ ρ = ρ := by
    calc
      _ = (ρ ≫ ρ ≫ ρ) ≫ ρ := by simp only [Category.assoc]
      _ = ρ := by rw [hcube, Category.id_comp]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [MonObj.mul_comp, cp_conjAut, Category.assoc, lift_fst,
      Category.id_comp, MonObj.one_comp, lift_fst_assoc, lift_snd_assoc]
    simpa only [MonObj.comp_mul, Category.comp_id, Category.assoc, MonObj.comp_one] using
      congrArg (fun f : E ⟶ E => fst E E ≫ f) hρ
  · have hconj : 𝟙 E * (ρ ≫ ρ) * (ρ ≫ ρ ≫ ρ ≫ ρ) = 1 := by
      rw [hfour]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hρ
    simp only [MonObj.mul_comp, cp_conjAut, Category.assoc, lift_snd,
      Category.id_comp, MonObj.one_comp, lift_fst_assoc, lift_snd_assoc]
    simpa only [MonObj.comp_mul, Category.comp_id, Category.assoc, MonObj.comp_one] using
      congrArg (fun f : E ⟶ E => snd E E ≫ f) hconj

private theorem cp_rankTwo_skew {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (hrank : Module.finrank ℚ V = 2)
    (J : Module.End ℚ V) (hJ : J ∘ₗ J = (-3 : ℚ) • LinearMap.id)
    (B : LinearMap.BilinForm ℚ V) (hB : B.IsAlt) :
    ∀ x y, B (J x) y = -B x (J y) := by
  classical
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℚ) (M := V) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hJv : J (J v) = (-3 : ℚ) • v := LinearMap.congr_fun hJ v
  have hli : LinearIndependent ℚ ![J v, v] := by
    rw [linearIndependent_fin2]
    refine ⟨hv, ?_⟩
    intro a ha
    change a • v = J v at ha
    have hh := congrArg J ha
    rw [map_smul, hJv, ← ha, smul_smul] at hh
    have heq : a * a = (-3 : ℚ) := (smul_left_injective ℚ hv) hh
    nlinarith [sq_nonneg a]
  let b := basisOfLinearIndependentOfCardEqFinrank hli
    (by simpa using hrank.symm)
  have hspan (x : V) : ∃ a c : ℚ, x = a • J v + c • v := by
    refine ⟨b.repr x 0, b.repr x 1, ?_⟩
    have hh := b.sum_repr x
    simpa only [Fin.sum_univ_two, b,
      coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hh.symm
  intro x y
  obtain ⟨a, c, rfl⟩ := hspan x
  obtain ⟨d, e, rfl⟩ := hspan y
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hJv,
    hB.self_eq_zero, smul_eq_mul]
  rw [← hB.neg_eq v (J v)]
  ring

section ProductRanks

variable (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom] [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom]

theorem cp_product_weil_ranks
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (WY : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) 3)
    (W : letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ Y)) 3)
    (hA : ∀ a, W.J (homPullback (fst A Y) 1 a) = homPullback (fst A Y) 1 (WA.J a))
    (hY : ∀ b, W.J (homPullback (snd A Y) 1 b) = homPullback (snd A Y) 1 (WY.J b)) :
    letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
    Module.finrank ℂ W.Vs = Module.finrank ℂ WA.Vs + Module.finrank ℂ WY.Vs ∧
      Module.finrank ℂ ↥(W.Vs ⊓ (abelianWeightOneHodgeStructure (A ⊗ Y)).H (1, 0)) =
        Module.finrank ℂ ↥(WA.Vs ⊓ (abelianWeightOneHodgeStructure A).H (1, 0)) +
          Module.finrank ℂ ↥(WY.Vs ⊓ (abelianWeightOneHodgeStructure Y).H (1, 0)) := by
  letI := (finiteBetti_abelian A).finite 1
  letI := (finiteBetti_abelian Y).finite 1
  letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
  let iA : A ⟶ A ⊗ Y := lift (𝟙 A) 1
  let iY : Y ⟶ A ⊗ Y := lift 1 (𝟙 Y)
  have : IsMonHom iA := by dsimp [iA]; simp only [Hom.one_def]; infer_instance
  have : IsMonHom iY := by dsimp [iY]; simp only [Hom.one_def]; infer_instance
  let FA := (homPullback (fst A Y) 1).baseChange ℂ
  let FY := (homPullback (snd A Y) 1).baseChange ℂ
  let GA := (homPullback iA 1).baseChange ℂ
  let GY := (homPullback iY 1).baseChange ℂ
  have hAA (x) : GA (FA x) = x := by
    simp only [GA, FA, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← spec_homPullback_comp, iA, lift_fst, spec_homPullback_id,
      LinearMap.baseChange_id, LinearMap.id_apply]
  have hAY (x) : GA (FY x) = 0 := by
    simp only [GA, FY, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← spec_homPullback_comp, iA, lift_snd, spec_homPullback_one,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  have hYA (x) : GY (FA x) = 0 := by
    simp only [GY, FA, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← spec_homPullback_comp, iY, lift_fst, spec_homPullback_one,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  have hYY (x) : GY (FY x) = x := by
    simp only [GY, FY, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← spec_homPullback_comp, iY, lift_snd, spec_homPullback_id,
      LinearMap.baseChange_id, LinearMap.id_apply]
  have hcat : fst A Y ≫ iA * (snd A Y ≫ iY) = 𝟙 (A ⊗ Y) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.mul_comp, iA, iY, MonObj.comp_one]
  have hsplit (z) : FA (GA z) + FY (GY z) = z := by
    have hh : homPullback (fst A Y) 1 ∘ₗ homPullback iA 1 +
        homPullback (snd A Y) 1 ∘ₗ homPullback iY 1 = LinearMap.id := by
      rw [← spec_homPullback_comp, ← spec_homPullback_comp,
        ← spec_homPullback_mul, hcat, spec_homPullback_id]
    have hc := congrArg (fun f : Module.End ℚ (HQ (A ⊗ Y) 1) => f.baseChange ℂ) hh
    exact LinearMap.congr_fun (by simpa only [LinearMap.baseChange_add,
      LinearMap.baseChange_comp, LinearMap.baseChange_id] using hc) z
  have hAc (x) : W.Jc (FA x) = FA (WA.Jc x) := by
    have hh : W.J ∘ₗ homPullback (fst A Y) 1 = homPullback (fst A Y) 1 ∘ₗ WA.J :=
      LinearMap.ext hA
    have hc := congrArg (fun f : HQ A 1 →ₗ[ℚ] HQ (A ⊗ Y) 1 => f.baseChange ℂ) hh
    exact LinearMap.congr_fun (by simpa only [LinearMap.baseChange_comp] using hc) x
  have hYc (x) : W.Jc (FY x) = FY (WY.Jc x) := by
    have hh : W.J ∘ₗ homPullback (snd A Y) 1 = homPullback (snd A Y) 1 ∘ₗ WY.J :=
      LinearMap.ext hY
    have hc := congrArg (fun f : HQ Y 1 →ₗ[ℚ] HQ (A ⊗ Y) 1 => f.baseChange ℂ) hh
    exact LinearMap.congr_fun (by simpa only [LinearMap.baseChange_comp] using hc) x
  have hGA (z) : GA (W.Jc z) = WA.Jc (GA z) := by
    calc
      _ = GA (W.Jc (FA (GA z) + FY (GY z))) := by rw [hsplit]
      _ = _ := by simp only [map_add, hAc, hYc, hAA, hAY, add_zero]
  have hGY (z) : GY (W.Jc z) = WY.Jc (GY z) := by
    calc
      _ = GY (W.Jc (FA (GA z) + FY (GY z))) := by rw [hsplit]
      _ = _ := by simp only [map_add, hAc, hYc, hYA, hYY, zero_add]
  have hFA (x) (hx : x ∈ WA.Vs) : FA x ∈ W.Vs := by
    rw [HodgeBlocks.WeilAction.Vs, Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hAc, hx, map_smul]
  have hFY (x) (hx : x ∈ WY.Vs) : FY x ∈ W.Vs := by
    rw [HodgeBlocks.WeilAction.Vs, Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hYc, hx, map_smul]
  have hGAe (z) (hz : z ∈ W.Vs) : GA z ∈ WA.Vs := by
    rw [HodgeBlocks.WeilAction.Vs, Module.End.mem_eigenspace_iff] at hz ⊢
    rw [← hGA, hz, map_smul]
  have hGYe (z) (hz : z ∈ W.Vs) : GY z ∈ WY.Vs := by
    rw [HodgeBlocks.WeilAction.Vs, Module.End.mem_eigenspace_iff] at hz ⊢
    rw [← hGY, hz, map_smul]
  have hrank := cp_split_submodule_rank FA FY GA GY hAA hAY hYA hYY hsplit
    WA.Vs WY.Vs W.Vs hFA hFY hGAe hGYe
  have hpiece := cp_split_submodule_rank FA FY GA GY hAA hAY hYA hYY hsplit
    (WA.Vs ⊓ (abelianWeightOneHodgeStructure A).H (1, 0))
    (WY.Vs ⊓ (abelianWeightOneHodgeStructure Y).H (1, 0))
    (W.Vs ⊓ (abelianWeightOneHodgeStructure (A ⊗ Y)).H (1, 0))
    (fun x hx => ⟨hFA x hx.1, spec_homPullback_hodgePiece_one (fst A Y) (1, 0)
      (Submodule.mem_map_of_mem hx.2)⟩)
    (fun x hx => ⟨hFY x hx.1, spec_homPullback_hodgePiece_one (snd A Y) (1, 0)
      (Submodule.mem_map_of_mem hx.2)⟩)
    (fun z hz => ⟨hGAe z hz.1, spec_homPullback_hodgePiece_one iA (1, 0)
      (Submodule.mem_map_of_mem hz.2)⟩)
    (fun z hz => ⟨hGYe z hz.1, spec_homPullback_hodgePiece_one iY (1, 0)
      (Submodule.mem_map_of_mem hz.2)⟩)
  exact ⟨hrank, hpiece⟩

end ProductRanks

/-- The exterior polarization vector depends linearly on the cohomology class.
Source: linearity of `TorusCohomology.cupWedgeEquiv`. -/
theorem cp_polarizationVec_smul (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (c : ℚ) (pol : HQ X 2) :
    polarizationVec (torusCohomology_cupProductOf X) (c • pol) =
      c • polarizationVec (torusCohomology_cupProductOf X) pol :=
  map_smul ((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm c pol

/-- Positive scaling of a class preserves positivity of its dual alternating form.
Source: `cp_polarisation_smul`, `cp_dualForm_smul_of_eq`. -/
theorem cp_scaled_pol_positive (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (c : ℚ) (hc : 0 < c) (pol : HQ X 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X) pol))
    (hscaled : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X) (c • pol)))
    (hPos : PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X) hη) :
    PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X) hscaled := by
  letI := (finiteBetti_abelian X).finite 1
  obtain ⟨P, hP⟩ := hPos
  obtain ⟨Q, hQ⟩ := cp_polarisation_smul (abelianWeightOneHodgeStructure X) P c⁻¹ (inv_pos.mpr hc)
  have hform : polarizationForm (torusCohomology_cupProductOf X) hscaled =
      c⁻¹ • polarizationForm (torusCohomology_cupProductOf X) hη := by
    ext x y
    exact cp_dualForm_smul_of_eq c hc.ne' hη hscaled (cp_polarizationVec_smul X c pol) x y
  refine ⟨Q, hQ.trans ?_⟩
  rw [hP, ← hform]

/-- Negating a quadratic Weil operator gives the conjugate action.
Source: the conjugation automorphism of an imaginary quadratic field. -/
def cp_negWeilAction {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {S : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (W : HodgeBlocks.WeilAction S d) :
    HodgeBlocks.WeilAction S d where
  J := -W.J
  J_sq := by
    ext x
    simpa only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg, neg_neg,
      LinearMap.smul_apply, LinearMap.id_apply] using LinearMap.congr_fun W.J_sq x
  preserves := by
    intro pq
    rintro _ ⟨x, hx, rfl⟩
    simp only [LinearMap.baseChange_neg, LinearMap.neg_apply]
    exact Submodule.neg_mem _ (W.preserves pq (Submodule.mem_map_of_mem hx))

section Surface

variable (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] [IsIntegral E.left] [Smooth E.hom]
  [IsProjective E.hom]

/-- The conjugate product operator restricts to the operator and its negative.
Source: `spec_homPullback_comp`, `spec_homPullback_mul`, the order-three relation. -/
theorem cp_conjAut_weil_restrictions (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) :
    (∀ x, cp_weilOperator (E ⊗ E) (cp_conjAut E ρ) (homPullback (fst E E) 1 x) =
      homPullback (fst E E) 1 (cp_weilOperator E ρ x)) ∧
    (∀ x, cp_weilOperator (E ⊗ E) (cp_conjAut E ρ) (homPullback (snd E E) 1 x) =
      homPullback (snd E E) 1 (-(cp_weilOperator E ρ x))) := by
  have hpA : homPullback (cp_conjAut E ρ) 1 ∘ₗ homPullback (fst E E) 1 =
      homPullback (fst E E) 1 ∘ₗ homPullback ρ 1 := by
    rw [← spec_homPullback_comp, ← spec_homPullback_comp]
    congr 1
    simp only [cp_conjAut, lift_fst]
  have hpY : homPullback (cp_conjAut E ρ) 1 ∘ₗ homPullback (snd E E) 1 =
      homPullback (snd E E) 1 ∘ₗ homPullback (ρ ≫ ρ) 1 := by
    rw [← spec_homPullback_comp, ← spec_homPullback_comp]
    congr 1
    simp only [cp_conjAut, lift_snd, Category.assoc]
  have hrel (x : HQ E 1) : homPullback (ρ ≫ ρ) 1 x = -(x + homPullback ρ 1 x) := by
    have hh := congrArg (fun f : E ⟶ E => homPullback f 1) hρ
    rw [spec_homPullback_mul, spec_homPullback_mul, spec_homPullback_id,
      spec_homPullback_one] at hh
    have hx := LinearMap.congr_fun hh x
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.zero_apply] at hx
    exact eq_neg_of_add_eq_zero_right hx
  constructor
  · intro x
    change homPullback (fst E E) 1 x + (2 : ℚ) •
        homPullback (cp_conjAut E ρ) 1 (homPullback (fst E E) 1 x) =
      homPullback (fst E E) 1 (x + (2 : ℚ) • homPullback ρ 1 x)
    rw [show homPullback (cp_conjAut E ρ) 1 (homPullback (fst E E) 1 x) =
      homPullback (fst E E) 1 (homPullback ρ 1 x) from LinearMap.congr_fun hpA x,
      map_add, map_smul]
  · intro x
    change homPullback (snd E E) 1 x + (2 : ℚ) •
        homPullback (cp_conjAut E ρ) 1 (homPullback (snd E E) 1 x) =
      homPullback (snd E E) 1 (-(x + (2 : ℚ) • homPullback ρ 1 x))
    rw [show homPullback (cp_conjAut E ρ) 1 (homPullback (snd E E) 1 x) =
      homPullback (snd E E) 1 (homPullback (ρ ≫ ρ) 1 x) from LinearMap.congr_fun hpY x,
      hrel]
    simp only [map_neg, map_add, map_smul]
    module

theorem cp_cm_surface_weilType_aux (ρ : E ⟶ E) [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) :
    letI := (finiteBetti_abelian (E ⊗ E)).finite 1
    W.IsWeilType := by
  letI := (finiteBetti_abelian E).finite 1
  letI := (finiteBetti_abelian (E ⊗ E)).finite 1
  let WE := cp_weilAction E ρ (cp_weilOperator_sq_aux E ρ hρ)
  let WN : HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure E) 3 :=
    { J := -WE.J
      J_sq := by
        ext x
        simpa only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg, neg_neg,
          LinearMap.smul_apply, LinearMap.id_apply] using LinearMap.congr_fun WE.J_sq x
      preserves := by
        intro pq
        rintro _ ⟨x, hx, rfl⟩
        simp only [LinearMap.baseChange_neg, LinearMap.neg_apply]
        exact Submodule.neg_mem _ (WE.preserves pq (Submodule.mem_map_of_mem hx)) }
  have hpA : homPullback (cp_conjAut E ρ) 1 ∘ₗ homPullback (fst E E) 1 =
      homPullback (fst E E) 1 ∘ₗ homPullback ρ 1 := by
    rw [← spec_homPullback_comp, ← spec_homPullback_comp]
    congr 1
    simp only [cp_conjAut, lift_fst]
  have hpY : homPullback (cp_conjAut E ρ) 1 ∘ₗ homPullback (snd E E) 1 =
      homPullback (snd E E) 1 ∘ₗ homPullback (ρ ≫ ρ) 1 := by
    rw [← spec_homPullback_comp, ← spec_homPullback_comp]
    congr 1
    simp only [cp_conjAut, lift_snd, Category.assoc]
  have hrel (x : HQ E 1) : homPullback (ρ ≫ ρ) 1 x = -(x + homPullback ρ 1 x) := by
    have hh := congrArg (fun f : E ⟶ E => homPullback f 1) hρ
    rw [spec_homPullback_mul, spec_homPullback_mul, spec_homPullback_id,
      spec_homPullback_one] at hh
    have hx := LinearMap.congr_fun hh x
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.zero_apply] at hx
    exact eq_neg_of_add_eq_zero_right hx
  have hA (x) : W.J (homPullback (fst E E) 1 x) = homPullback (fst E E) 1 (WE.J x) := by
    rw [hJ]
    change homPullback (fst E E) 1 x + (2 : ℚ) •
        homPullback (cp_conjAut E ρ) 1 (homPullback (fst E E) 1 x) =
      homPullback (fst E E) 1 (x + (2 : ℚ) • homPullback ρ 1 x)
    rw [show homPullback (cp_conjAut E ρ) 1 (homPullback (fst E E) 1 x) =
      homPullback (fst E E) 1 (homPullback ρ 1 x) from LinearMap.congr_fun hpA x,
      map_add, map_smul]
  have hY (x) : W.J (homPullback (snd E E) 1 x) = homPullback (snd E E) 1 (WN.J x) := by
    rw [hJ]
    change homPullback (snd E E) 1 x + (2 : ℚ) •
        homPullback (cp_conjAut E ρ) 1 (homPullback (snd E E) 1 x) =
      homPullback (snd E E) 1 (-(x + (2 : ℚ) • homPullback ρ 1 x))
    rw [show homPullback (cp_conjAut E ρ) 1 (homPullback (snd E E) 1 x) =
      homPullback (snd E E) 1 (homPullback (ρ ≫ ρ) 1 x) from LinearMap.congr_fun hpY x,
      hrel]
    simp only [map_neg, map_add, map_smul]
    module
  have hneg : WN.Vs = WE.Vsbar := by
    ext x
    change x ∈ Module.End.eigenspace ((-WE.J).baseChange ℂ) (HodgeBlocks.WeilAction.omegaC 3) ↔
      x ∈ Module.End.eigenspace WE.Jc (-HodgeBlocks.WeilAction.omegaC 3)
    simp only [Module.End.mem_eigenspace_iff, LinearMap.baseChange_neg,
      LinearMap.neg_apply, neg_eq_iff_eq_neg, neg_smul]
  have ⟨hrank, hpiece⟩ := cp_product_weil_ranks E E WE WN W hA hY
  have hH := h10_sup_h01_eq_top (finiteBetti_abelian E) (spec_bettiDeRhamIso_abelian E)
    (hodgeDecomposition_of_abelian E) (torusCohomology_cupProductOf E)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (WE.Vs ⊓ (abelianWeightOneHodgeStructure E).H (1, 0))
    (WE.Vs ⊓ (abelianWeightOneHodgeStructure E).H (0, 1))
  rw [WE.inf_H10_H01_Vs, ← WE.Vs_eq_sup hH, finrank_bot, add_zero] at hsum
  have hconj : Module.finrank ℂ ↥(WE.Vsbar ⊓ (abelianWeightOneHodgeStructure E).H (1, 0)) =
      Module.finrank ℂ ↥(WE.Vs ⊓ (abelianWeightOneHodgeStructure E).H (0, 1)) := by
    rw [← WE.map_inf_Vs_H01_sigmaQ, HodgeBlocks.WeilAction.finrank_map_sigmaQ]
  rw [hneg, WE.finrank_Vsbar_eq_Vs] at hrank
  rw [hneg, hconj] at hpiece
  change 2 * _ = _
  omega

theorem cp_curve_rosati_aux (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) (pol : HQ E 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf E) pol)) :
    letI := (finiteBetti_abelian E).finite 1
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf E) pol) (cp_weilOperator E ρ) := by
  letI := (finiteBetti_abelian E).finite 1
  apply (isRosatiSkew_iff_dualForm hη _).mpr
  apply cp_rankTwo_skew _ (cp_weilOperator E ρ) (cp_weilOperator_sq_aux E ρ hρ)
    (dualForm hη) (isAlt_dualForm hη)
  rw [(torusCohomology_cupProductOf E).finrank_eq, hE]


end Surface

theorem cp_surface_weilClassesAlgebraic_aux (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] (hY : TopologicalSpace.dim Y.left = 2)
    {d : ℚ} (hd : 0 < d)
    (W : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) d)
    (hW : letI := (finiteBetti_abelian Y).finite 1; W.IsWeilType) :
    letI := (finiteBetti_abelian Y).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
      (hodgeDecomposition_of_abelian Y) (torusCohomology_cupProductOf Y) W hW := by
  letI := (finiteBetti_abelian Y).finite 1
  let k := Module.finrank ℂ ↥(W.Vs ⊓
    (abelianVarietyCohomologyOf (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
      (hodgeDecomposition_of_abelian Y) (torusCohomology_cupProductOf Y)).weight1.H (1, 0))
  have hk := two_mul_finrank_vs_inf_h10_eq (finiteBetti_abelian Y)
    (spec_bettiDeRhamIso_abelian Y) (hodgeDecomposition_of_abelian Y)
    (torusCohomology_cupProductOf Y) hd W hW
  change 2 * k = TopologicalSpace.dim Y.left at hk
  rw [hY] at hk
  have hk1 : k = 1 := by omega
  have hle : Hdg^k(Y; ℚ) ≤ algebraicCycleClassSpan Y k := by
    rw [hk1]
    exact chowG_lefschetzOneOne_abelian Y
  exact (abelian_weilClassOf_le_hdg Y W hW).trans hle

/-! ### C4 -/

section Member

variable (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom] [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom]

theorem cp_product_weilAction_aux
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (WY : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) 3) :
    ∃ W : (letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
        HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ Y)) 3),
      (∀ a, W.J (homPullback (fst A Y) 1 a) = homPullback (fst A Y) 1 (WA.J a)) ∧
        ∀ b, W.J (homPullback (snd A Y) 1 b) = homPullback (snd A Y) 1 (WY.J b) := by
  letI := (finiteBetti_abelian A).finite 1
  letI := (finiteBetti_abelian Y).finite 1
  letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
  let iA : A ⟶ A ⊗ Y := lift (𝟙 A) 1
  let iY : Y ⟶ A ⊗ Y := lift 1 (𝟙 Y)
  have : IsMonHom iA := by dsimp [iA]; simp only [Hom.one_def]; infer_instance
  have : IsMonHom iY := by dsimp [iY]; simp only [Hom.one_def]; infer_instance
  have hAA (a : HQ A 1) : homPullback iA 1 (homPullback (fst A Y) 1 a) = a := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp]
    simp only [iA, lift_fst, spec_homPullback_id, LinearMap.id_apply]
  have hAY (b : HQ Y 1) : homPullback iA 1 (homPullback (snd A Y) 1 b) = 0 := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp]
    simp only [iA, lift_snd, spec_homPullback_one, LinearMap.zero_apply]
  have hYA (a : HQ A 1) : homPullback iY 1 (homPullback (fst A Y) 1 a) = 0 := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp]
    simp only [iY, lift_fst, spec_homPullback_one, LinearMap.zero_apply]
  have hYY (b : HQ Y 1) : homPullback iY 1 (homPullback (snd A Y) 1 b) = b := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp]
    simp only [iY, lift_snd, spec_homPullback_id, LinearMap.id_apply]
  let T : Module.End ℚ (HQ (A ⊗ Y) 1) :=
    homPullback (fst A Y) 1 ∘ₗ WA.J ∘ₗ homPullback iA 1 +
      homPullback (snd A Y) 1 ∘ₗ WY.J ∘ₗ homPullback iY 1
  have hTA (a) : T (homPullback (fst A Y) 1 a) = homPullback (fst A Y) 1 (WA.J a) := by
    simp only [T, LinearMap.add_apply, LinearMap.comp_apply, hAA, hYA, map_zero, add_zero]
  have hTY (b) : T (homPullback (snd A Y) 1 b) = homPullback (snd A Y) 1 (WY.J b) := by
    simp only [T, LinearMap.add_apply, LinearMap.comp_apply, hAY, hYY, map_zero, zero_add]
  refine ⟨{ J := T, J_sq := ?_, preserves := ?_ }, hTA, hTY⟩
  · ext x
    obtain ⟨⟨a, b⟩, rfl⟩ := (cp_kunneth_H1_aux A Y).surjective x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      map_add, hTA, hTY]
    have hA := LinearMap.congr_fun WA.J_sq a
    have hY := LinearMap.congr_fun WY.J_sq b
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hA hY
    rw [hA, hY, map_smul, map_smul]
  · intro pq
    rintro _ ⟨x, hx, rfl⟩
    simp only [T, LinearMap.baseChange_add, LinearMap.baseChange_comp,
      LinearMap.add_apply, LinearMap.comp_apply]
    apply Submodule.add_mem
    · apply spec_homPullback_hodgePiece_one (fst A Y) pq
      apply Submodule.mem_map_of_mem
      apply WA.preserves pq
      apply Submodule.mem_map_of_mem
      exact spec_homPullback_hodgePiece_one iA pq (Submodule.mem_map_of_mem hx)
    · apply spec_homPullback_hodgePiece_one (snd A Y) pq
      apply Submodule.mem_map_of_mem
      apply WY.preserves pq
      apply Submodule.mem_map_of_mem
      exact spec_homPullback_hodgePiece_one iY pq (Submodule.mem_map_of_mem hx)

theorem cp_product_weilType_aux
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (hWA : letI := (finiteBetti_abelian A).finite 1; WA.IsWeilType)
    (WY : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) 3)
    (hWY : letI := (finiteBetti_abelian Y).finite 1; WY.IsWeilType)
    (W : letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ Y)) 3)
    (hA : ∀ a, W.J (homPullback (fst A Y) 1 a) = homPullback (fst A Y) 1 (WA.J a))
    (hY : ∀ b, W.J (homPullback (snd A Y) 1 b) = homPullback (snd A Y) 1 (WY.J b)) :
    letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
    W.IsWeilType := by
  have ⟨hrank, hpiece⟩ := cp_product_weil_ranks A Y WA WY W hA hY
  change 2 * _ = _ at hWA hWY ⊢
  rw [hrank, hpiece]
  omega

/-- Positivity of a product polarization follows from the two factor polarizations.
Source: `cp_product_dualForm`, `cp_polarisation_sum`. -/
theorem cp_product_pol_positive (polA : HQ A 2) (polY : HQ Y 2)
    (hA : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) polA))
    (hY : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf Y) polY))
    (hPosA : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hA)
    (hPosY : PolarizationPositive (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
      (hodgeDecomposition_of_abelian Y) (torusCohomology_cupProductOf Y) hY)
    (hP : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (A ⊗ Y))
      (cp_productPol A Y polA polY))) :
    PolarizationPositive (finiteBetti_abelian (A ⊗ Y)) (spec_bettiDeRhamIso_abelian (A ⊗ Y))
      (hodgeDecomposition_of_abelian (A ⊗ Y)) (torusCohomology_cupProductOf (A ⊗ Y)) hP := by
  letI := (finiteBetti_abelian A).finite 1
  letI := (finiteBetti_abelian Y).finite 1
  letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
  obtain ⟨PA, hPA⟩ := hPosA
  obtain ⟨PY, hPY⟩ := hPosY
  let iA : A ⟶ A ⊗ Y := lift (𝟙 A) 1
  let iY : Y ⟶ A ⊗ Y := lift 1 (𝟙 Y)
  have : IsMonHom iA := by dsimp [iA]; simp only [Hom.one_def]; infer_instance
  have : IsMonHom iY := by dsimp [iY]; simp only [Hom.one_def]; infer_instance
  let p := homPullback iA 1
  let q := homPullback iY 1
  have hf : polarizationForm (torusCohomology_cupProductOf (A ⊗ Y)) hP =
      PA.form.compl₁₂ p p + PY.form.compl₁₂ q q := by
    ext x y
    rw [hPA, hPY]
    exact cp_product_dualForm A Y polA polY hA hY hP x y
  have hnd : (PA.form.compl₁₂ p p + PY.form.compl₁₂ q q).Nondegenerate := by
    rw [← hf]
    exact nondegenerate_polarizationForm (torusCohomology_cupProductOf (A ⊗ Y)) hP
  have hinj (x) (hp : p.baseChange ℂ x = 0) (hq : q.baseChange ℂ x = 0) : x = 0 := by
    have hcat : fst A Y ≫ iA * (snd A Y ≫ iY) = 𝟙 (A ⊗ Y) := by
      apply CartesianMonoidalCategory.hom_ext <;>
        simp [MonObj.mul_comp, iA, iY, MonObj.comp_one]
    have hl : homPullback (fst A Y) 1 ∘ₗ p + homPullback (snd A Y) 1 ∘ₗ q = LinearMap.id := by
      rw [← spec_homPullback_comp, ← spec_homPullback_comp,
        ← spec_homPullback_mul, hcat, spec_homPullback_id]
    have hc := congrArg (fun f : Module.End ℚ (HQ (A ⊗ Y) 1) => f.baseChange ℂ) hl
    have hx := LinearMap.congr_fun hc x
    simp only [LinearMap.baseChange_add, LinearMap.baseChange_comp, LinearMap.baseChange_id,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hp, hq, map_zero, zero_add] at hx
    exact hx.symm
  obtain ⟨P, hform⟩ := cp_polarisation_sum (abelianWeightOneHodgeStructure A)
    (abelianWeightOneHodgeStructure Y) (abelianWeightOneHodgeStructure (A ⊗ Y)) PA PY p q
    (fun pq x hx => spec_homPullback_hodgePiece_one iA pq (Submodule.mem_map_of_mem hx))
    (fun pq x hx => spec_homPullback_hodgePiece_one iY pq (Submodule.mem_map_of_mem hx)) hinj hnd
  exact ⟨P, hform.trans hf.symm⟩

/-- The product class is Rosati-compatible with an action restricting to the two given actions.
Source: `cp_sumVec_rosati`, `cp_map_rosati`, degree-one Künneth. -/
theorem cp_product_pol_rosati
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (WY : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) 3)
    (W : letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ Y)) 3)
    (hA : ∀ a, W.J (homPullback (fst A Y) 1 a) = homPullback (fst A Y) 1 (WA.J a))
    (hY : ∀ b, W.J (homPullback (snd A Y) 1 b) = homPullback (snd A Y) 1 (WY.J b))
    (polA : HQ A 2) (polY : HQ Y 2)
    (hηA : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) polA))
    (hηY : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf Y) polY))
    (hRA : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) polA) WA.J)
    (hRY : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf Y) polY) WY.J) :
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (A ⊗ Y))
      (cp_productPol A Y polA polY)) W.J := by
  letI := (finiteBetti_abelian A).finite 1
  letI := (finiteBetti_abelian Y).finite 1
  letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
  let f := (homPullback (fst A Y) 1).coprod (homPullback (snd A Y) 1)
  let e := LinearEquiv.ofBijective f (cp_kunneth_H1_aux A Y)
  have hinl : e.toLinearMap ∘ₗ LinearMap.inl ℚ (HQ A 1) (HQ Y 1) = homPullback (fst A Y) 1 := by
    ext x
    change homPullback (fst A Y) 1 x + homPullback (snd A Y) 1 0 = homPullback (fst A Y) 1 x
    rw [map_zero, add_zero]
  have hinr : e.toLinearMap ∘ₗ LinearMap.inr ℚ (HQ A 1) (HQ Y 1) = homPullback (snd A Y) 1 := by
    ext x
    change homPullback (fst A Y) 1 0 + homPullback (snd A Y) 1 x = homPullback (snd A Y) 1 x
    rw [map_zero, zero_add]
  have hv : exteriorPower.map 2 e.toLinearMap
      (cp_sumVec (polarizationVec (torusCohomology_cupProductOf A) polA)
        (polarizationVec (torusCohomology_cupProductOf Y) polY)) =
      polarizationVec (torusCohomology_cupProductOf (A ⊗ Y)) (cp_productPol A Y polA polY) := by
    rw [cp_sumVec, map_add]
    simp only [cp_exterior_map_map]
    rw [hinl, hinr, ← cp_product_polarizationVec A Y]
  rw [← hv]
  apply cp_map_rosati e (cp_sumVec_nondegenerate hηA hηY) (WA.J.prodMap WY.J) W.J
  · rintro ⟨a, b⟩
    change W.J (homPullback (fst A Y) 1 a + homPullback (snd A Y) 1 b) =
      homPullback (fst A Y) 1 (WA.J a) + homPullback (snd A Y) 1 (WY.J b)
    rw [map_add, hA, hY]
  · exact cp_sumVec_rosati hηA hηY WA.J WY.J hRA hRY

/-- Orthogonal Künneth splitting multiplies the Weil determinant classes.
Source: `cp_weilDetClass_product`, `cp_H1Equiv_map_sumVec`. -/
theorem cp_product_weilDatumClass
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (WY : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) 3)
    (W : letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ Y)) 3)
    (hA : ∀ a, W.J (homPullback (fst A Y) 1 a) = homPullback (fst A Y) 1 (WA.J a))
    (hY : ∀ b, W.J (homPullback (snd A Y) 1 b) = homPullback (snd A Y) 1 (WY.J b))
    (polA : HQ A 2) (polY : HQ Y 2)
    (hηA : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) polA))
    (hηY : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf Y) polY))
    (hRA : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) polA) WA.J)
    (hRY : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf Y) polY) WY.J)
    (hP : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (A ⊗ Y))
      (cp_productPol A Y polA polY)))
    (hRP : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (A ⊗ Y))
      (cp_productPol A Y polA polY)) W.J) :
    weilDatumClass (finiteBetti_abelian (A ⊗ Y)) (spec_bettiDeRhamIso_abelian (A ⊗ Y))
      (hodgeDecomposition_of_abelian (A ⊗ Y)) (torusCohomology_cupProductOf (A ⊗ Y)) W hP hRP =
    weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) WA hηA hRA *
    weilDatumClass (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
      (hodgeDecomposition_of_abelian Y) (torusCohomology_cupProductOf Y) WY hηY hRY := by
  letI := (finiteBetti_abelian A).finite 1
  letI := (finiteBetti_abelian Y).finite 1
  letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
  have hJ (x : HQ A 1 × HQ Y 1) : W.J (cp_H1Equiv A Y x) =
      cp_H1Equiv A Y (WA.J x.1, WY.J x.2) := by
    change W.J (homPullback (fst A Y) 1 x.1 + homPullback (snd A Y) 1 x.2) = _
    rw [map_add, hA, hY]
    rfl
  have hE (x y : HQ A 1 × HQ Y 1) :
      polarizationForm (torusCohomology_cupProductOf (A ⊗ Y)) hP
        (cp_H1Equiv A Y x) (cp_H1Equiv A Y y) =
      polarizationForm (torusCohomology_cupProductOf A) hηA x.1 y.1 +
        polarizationForm (torusCohomology_cupProductOf Y) hηY x.2 y.2 := by
    exact (cp_dualForm_map_of_eq (cp_H1Equiv A Y) (cp_sumVec_nondegenerate hηA hηY) hP
      (cp_H1Equiv_map_sumVec A Y polA polY) x y).trans (cp_dualForm_sumVec hηA hηY x y)
  exact cp_weilDetClass_product _ _ _ ⟨WA.J, WA.J_sq⟩ ⟨WY.J, WY.J_sq⟩ ⟨W.J, W.J_sq⟩
    ((isRosatiSkew_iff_dualForm hηA WA.J).mp hRA)
    ((isRosatiSkew_iff_dualForm hηY WY.J).mp hRY)
    ((isRosatiSkew_iff_dualForm hP W.J).mp hRP)
    (isAlt_polarizationForm _ hηA) (isAlt_polarizationForm _ hηY) (isAlt_polarizationForm _ hP)
    (nondegenerate_polarizationForm _ hηA) (nondegenerate_polarizationForm _ hηY)
    (nondegenerate_polarizationForm _ hP) (cp_H1Equiv A Y) hJ hE

theorem cp_product_polarization_aux
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (polA : HQ A 2)
    (hηA : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) polA))
    (hRA : letI := (finiteBetti_abelian A).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) polA) WA.J)
    (hPosA : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hηA)
    (WY : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) 3)
    (polY : HQ Y 2)
    (hηY : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf Y) polY))
    (hRY : letI := (finiteBetti_abelian Y).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf Y) polY) WY.J)
    (hPosY : PolarizationPositive (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
      (hodgeDecomposition_of_abelian Y) (torusCohomology_cupProductOf Y) hηY)
    (W : letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ Y)) 3)
    (hA : ∀ a, W.J (homPullback (fst A Y) 1 a) = homPullback (fst A Y) 1 (WA.J a))
    (hY : ∀ b, W.J (homPullback (snd A Y) 1 b) = homPullback (snd A Y) 1 (WY.J b)) :
    ∃ hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (A ⊗ Y))
        (cp_productPol A Y polA polY)),
      ∃ hR : (letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
        IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (A ⊗ Y))
          (cp_productPol A Y polA polY)) W.J),
        PolarizationPositive (finiteBetti_abelian (A ⊗ Y)) (spec_bettiDeRhamIso_abelian (A ⊗ Y))
          (hodgeDecomposition_of_abelian (A ⊗ Y)) (torusCohomology_cupProductOf (A ⊗ Y)) hη ∧
        weilDatumClass (finiteBetti_abelian (A ⊗ Y)) (spec_bettiDeRhamIso_abelian (A ⊗ Y))
            (hodgeDecomposition_of_abelian (A ⊗ Y)) (torusCohomology_cupProductOf (A ⊗ Y))
            W hη hR =
          weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
              (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) WA hηA hRA *
            weilDatumClass (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
              (hodgeDecomposition_of_abelian Y) (torusCohomology_cupProductOf Y) WY hηY hRY := by
  let hη := cp_product_pol_nondegenerate A Y polA polY hηA hηY
  let hR := cp_product_pol_rosati A Y WA WY W hA hY polA polY hηA hηY hRA hRY
  refine ⟨hη, hR, cp_product_pol_positive A Y polA polY hηA hηY hPosA hPosY hη, ?_⟩
  exact cp_product_weilDatumClass A Y WA WY W hA hY polA polY hηA hηY hRA hRY hη hR

end Member

section CMSurfacePolarization

variable (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] [IsIntegral E.left] [Smooth E.hom]
  [IsProjective E.hom]

theorem cp_cm_surface_polarization_aux (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E)
    [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) (pol : HQ E 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf E) pol))
    (hPos : PolarizationPositive (finiteBetti_abelian E) (spec_bettiDeRhamIso_abelian E)
      (hodgeDecomposition_of_abelian E) (torusCohomology_cupProductOf E) hη)
    (m : ℕ) (hm : 0 < m)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) :
    ∃ hηY : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (E ⊗ E))
        (cp_productPol E E pol ((m : ℚ) • pol))),
      ∃ hR : (letI := (finiteBetti_abelian (E ⊗ E)).finite 1
        IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (E ⊗ E))
          (cp_productPol E E pol ((m : ℚ) • pol))) W.J),
        PolarizationPositive (finiteBetti_abelian (E ⊗ E)) (spec_bettiDeRhamIso_abelian (E ⊗ E))
          (hodgeDecomposition_of_abelian (E ⊗ E)) (torusCohomology_cupProductOf (E ⊗ E)) hηY ∧
        weilDatumClass (finiteBetti_abelian (E ⊗ E)) (spec_bettiDeRhamIso_abelian (E ⊗ E))
          (hodgeDecomposition_of_abelian (E ⊗ E)) (torusCohomology_cupProductOf (E ⊗ E))
          W hηY hR = cp_ratClass (-(m : ℚ)) (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hm.ne')) := by
  letI := (finiteBetti_abelian E).finite 1
  letI := (finiteBetti_abelian (E ⊗ E)).finite 1
  let WE := cp_weilAction E ρ (cp_weilOperator_sq_aux E ρ hρ)
  let WN := cp_negWeilAction WE
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hm0 : (m : ℚ) ≠ 0 := hmQ.ne'
  have hRA : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf E) pol) WE.J :=
    cp_curve_rosati_aux E hE ρ hρ pol hη
  have hηm : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf E) ((m : ℚ) • pol)) := by
    rw [cp_polarizationVec_smul]
    exact cp_smul_nondegenerate (m : ℚ) hm0 hη
  have hRm : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf E)
      ((m : ℚ) • pol)) WN.J := by
    rw [cp_polarizationVec_smul]
    exact cp_smul_rosati (m : ℚ) hm0 hη (cp_smul_nondegenerate (m : ℚ) hm0 hη)
      (-WE.J) (cp_neg_rosati hη WE.J hRA)
  have hPosm := cp_scaled_pol_positive E (m : ℚ) hmQ pol hη hηm hPos
  have hr := cp_conjAut_weil_restrictions E ρ hρ
  have hA (x) : W.J (homPullback (fst E E) 1 x) = homPullback (fst E E) 1 (WE.J x) := by
    rw [hJ]
    exact hr.1 x
  have hY (x) : W.J (homPullback (snd E E) 1 x) = homPullback (snd E E) 1 (WN.J x) := by
    rw [hJ]
    exact hr.2 x
  obtain ⟨hηY, hR, hPosY, hclass⟩ := cp_product_polarization_aux E E
    WE pol hη hRA hPos WN ((m : ℚ) • pol) hηm hRm hPosm W hA hY
  refine ⟨hηY, hR, hPosY, hclass.trans ?_⟩
  have hdim : Module.finrank ℚ (HQ E 1) = 2 := by
    rw [(torusCohomology_cupProductOf E).finrank_eq, hE]
  have hform : polarizationForm (torusCohomology_cupProductOf E) hηm =
      (m : ℚ)⁻¹ • polarizationForm (torusCohomology_cupProductOf E) hη := by
    ext x y
    exact cp_dualForm_smul_of_eq (m : ℚ) hm0 hη hηm (cp_polarizationVec_smul E (m : ℚ) pol) x y
  exact cp_rankTwo_compensation_class_of_eq hdim _ ⟨WE.J, WE.J_sq⟩
    ((isRosatiSkew_iff_dualForm hη WE.J).mp hRA)
    (isAlt_polarizationForm _ hη) (nondegenerate_polarizationForm _ hη)
    (m : ℚ) hm0 _ hform ((isRosatiSkew_iff_dualForm hηm WN.J).mp hRm)
    (isAlt_polarizationForm _ hηm) (nondegenerate_polarizationForm _ hηm)

end CMSurfacePolarization

end HodgeLean.Foundations.Program

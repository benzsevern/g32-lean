import HodgeLean.Foundations.HodgeGroupAlgebraicDefs
import HodgeLean.Foundations.HodgeGroupAlgebraicDescent
import HodgeLean.Foundations.HodgeGroupAlgebraicConnected
import HodgeLean.Foundations.HodgeGroupAlgebraicLie
import HodgeLean.Foundations.HodgeGroupAlgebraicGkLie
import HodgeLean.Foundations.HodgeGroupAlgebraicGkCounterexample
import HodgeLean.Foundations.HodgeGroupAlgebraicGkConn
import HodgeLean.Adapters.AbelianCMDataDefs
import HodgeLean.Foundations.HodgeGroupAlgebraicBridge
import HodgeLean.Foundations.HodgeGroupAlgebraicRotation
import HodgeLean.Foundations.MatrixAlgGroupLie

/-! # Proof obligations for the Track G2 specification (the Hodge group and `G_k` as algebraic
`ℚ`-groups) -/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing

namespace HodgeLean.Foundations

open MvPolynomial
open scoped TensorProduct

section General

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)

omit [Module ℚ V] in
/-- An intersection of `ℚ`-algebraic subgroups is a `ℚ`-algebraic subgroup: its equations are
the union of the equations.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.11.3 and §1.1. -/
theorem g2h_isRatAlgSubgroup_sInter {F : Set (Set (Matrix.GeneralLinearGroup (Fin n) ℂ))}
    (hF : ∀ G ∈ F, g2_IsRatAlgSubgroup G) : g2_IsRatAlgSubgroup (⋂₀ F) := by
  choose S hS using fun G (hG : G ∈ F) => (hF G hG).1
  refine ⟨⟨⋃ G, ⋃ hG : G ∈ F, S G hG, ?_⟩, fun G hG => (hF G hG).2.1,
    fun x hx y hy G hG => (hF G hG).2.2.1 x (hx G hG) y (hy G hG),
    fun x hx G hG => (hF G hG).2.2.2 x (hx G hG)⟩
  ext g
  simp only [Set.mem_sInter, g2_ratZeroSet, Set.mem_iUnion, Set.mem_ofPred_eq,
    forall_exists_index]
  constructor
  · intro h f G hG hf
    have := h G hG
    rw [hS G hG] at this
    exact this f hf
  · intro h G hG
    rw [hS G hG]
    exact fun f hf => h f G hG hf

theorem g2_isRatAlgSubgroup_hodgeGroup_aux (b : Module.Basis (Fin n) ℚ V) :
    g2_IsRatAlgSubgroup (g2_hodgeGroup H hH b) :=
  g2h_isRatAlgSubgroup_sInter fun _ hG => hG.1

theorem g2_circleImage_subset_hodgeGroup_aux (b : Module.Basis (Fin n) ℚ V) :
    g2_circleImage H hH b ⊆ g2_hodgeGroup H hH b :=
  Set.subset_sInter fun _ hG => hG.2

theorem g2_hodgeGroup_eq_ratClosure_aux (b : Module.Basis (Fin n) ℚ V) :
    g2_hodgeGroup H hH b =
      g2_ratClosure (Subgroup.closure (g2_galoisOrbit (g2_circleImage H hH b)) :
        Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) := by
  set C := g2_circleImage H hH b
  set Γ := Subgroup.closure (g2_galoisOrbit C)
  have hΓ : g2h_GaloisStable (Γ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) :=
    g2h_galoisStable_closure (g2h_galoisStable_galoisOrbit C)
  have hCΓ : C ⊆ Γ := fun g hg => Subgroup.subset_closure
    (Set.mem_iUnion.mpr ⟨RingEquiv.refl ℂ, g, hg, by ext; simp⟩)
  apply le_antisymm
  · exact Set.sInter_subset_of_mem
      ⟨g2h_isRatAlgSubgroup_ratClosure Γ hΓ, hCΓ.trans fun g hg _ hq => hq g hg⟩
  · obtain ⟨⟨S, hS⟩, h1, hm, hi⟩ := g2_isRatAlgSubgroup_hodgeGroup_aux H hH b
    have hGal : g2h_GaloisStable (g2_hodgeGroup H hH b) := hS ▸ g2h_galoisStable_ratZeroSet S
    have hOrb : g2_galoisOrbit C ⊆ g2_hodgeGroup H hH b := by
      intro g hg
      obtain ⟨σ, x, hx, rfl⟩ := Set.mem_iUnion.mp hg
      exact hGal σ x (g2_circleImage_subset_hodgeGroup_aux H hH b hx)
    let Hsub : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
      { carrier := g2_hodgeGroup H hH b
        mul_mem' := fun {x y} hx hy => hm x hx y hy
        one_mem' := h1
        inv_mem' := fun {x} hx => hi x hx }
    have hΓH : (Γ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) ⊆ g2_hodgeGroup H hH b :=
      (Subgroup.closure_le Hsub).mpr hOrb
    intro x hx
    rw [hS]
    intro f hf
    refine hx f fun g hg => ?_
    have := hΓH hg
    rw [hS] at this
    exact this f hf

theorem g2_hodgeGroup_isConnected_aux (b : Module.Basis (Fin n) ℚ V) :
    @IsConnected _ (g1_zariski ℂ n) (g2_hodgeGroup H hH b) := by
  let _ := g1_zariski ℂ n
  rw [g2_hodgeGroup_eq_ratClosure_aux,
    g2h_ratClosure_eq_closure (g2h_galoisStable_closure (g2h_galoisStable_galoisOrbit _))]
  have h1 := g2h_one_mem_circleImage H hH b
  refine IsConnected.closure (g2h_isConnected_closure_of_connected
    (g2h_isConnected_galoisOrbit (g2h_isConnected_circleImage H hH b) h1)
    (Set.mem_iUnion.mpr ⟨RingEquiv.refl ℂ, 1, h1, map_one _⟩) fun x hx => ?_)
  exact g2h_inv_mem_galoisOrbit (fun y hy => g2h_inv_mem_circleImage H hH b hy) hx

theorem g2_lie_hodgeGroup_aux (b : Module.Basis (Fin n) ℚ V) :
    g1_lieOfSet (g2_hodgeGroup H hH b) =
      (complexSpan (hodgeLieAlgebra H hH).toSubmodule).map
        (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
          (Algebra.TensorProduct.basis ℂ b)).toLinearMap :=
  g2l_lie_hodgeGroup H hH b

theorem g2_isRatAlgSubgroup_gkGroup_aux (b : Module.Basis (Fin n) ℚ V)
    (E : LinearMap.BilinForm ℚ V) (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V)
    {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V)) :
    g2_IsRatAlgSubgroup (g2_gkGroup b E R J d) :=
  g2k_isRatAlgSubgroup_gkGroup b E R J hd hJ

theorem g2_mem_gkGroup_iff_aux (b : Module.Basis (Fin n) ℚ V)
    (E : LinearMap.BilinForm ℚ V) (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V)
    {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V))
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g ∈ g2_gkGroup b E R J d ↔
      (∀ r ∈ R, (g : Matrix (Fin n) (Fin n) ℂ) * (LinearMap.toMatrix b b r).map (algebraMap ℚ ℂ) =
          (LinearMap.toMatrix b b r).map (algebraMap ℚ ℂ) * g) ∧
      (g : Matrix (Fin n) (Fin n) ℂ) * (LinearMap.toMatrix b b J).map (algebraMap ℚ ℂ) =
          (LinearMap.toMatrix b b J).map (algebraMap ℚ ℂ) * g ∧
      Matrix.transpose (g : Matrix (Fin n) (Fin n) ℂ) *
          (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) * g =
        (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) ∧
      ((g : Matrix (Fin n) (Fin n) ℂ) *
          ((1 / 2 : ℂ) • (1 - (Complex.I / ((Real.sqrt d : ℝ) : ℂ)) •
            (LinearMap.toMatrix b b J).map (algebraMap ℚ ℂ))) +
        (1 - (1 / 2 : ℂ) • (1 - (Complex.I / ((Real.sqrt d : ℝ) : ℂ)) •
            (LinearMap.toMatrix b b J).map (algebraMap ℚ ℂ)))).det = 1 ∧
      ((g : Matrix (Fin n) (Fin n) ℂ) *
          (1 - (1 / 2 : ℂ) • (1 - (Complex.I / ((Real.sqrt d : ℝ) : ℂ)) •
            (LinearMap.toMatrix b b J).map (algebraMap ℚ ℂ))) +
        (1 / 2 : ℂ) • (1 - (Complex.I / ((Real.sqrt d : ℝ) : ℂ)) •
            (LinearMap.toMatrix b b J).map (algebraMap ℚ ℂ))).det = 1 :=
  g2k_mem_gkGroup_iff b E R J hd hJ g

theorem g2_lie_gkGroup_aux (b : Module.Basis (Fin n) ℚ V)
    (E : LinearMap.BilinForm ℚ V) (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V)
    {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V)) :
    g1_lieOfSet (g2_gkGroup b E R J d) =
      (complexSpan (gkLie E R J).toSubmodule).map
        (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
          (Algebra.TensorProduct.basis ℂ b)).toLinearMap := by
  ext Y
  rw [g2k_lieOfSet_gkGroup b E R J hd hJ, g2k_mem_map_complexSpan_gkLie_iff]

theorem g2_gkGroup_isConnected_adjoin_aux (b : Module.Basis (Fin n) ℚ V)
    (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V) {d : ℚ} (hd : 0 < d)
    (hJ : J * J = (-d) • (1 : Module.End ℚ V)) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hskew : ∀ x y, E (J x) y = -E x (J y)) :
    @IsConnected _ (g1_zariski ℂ n) (g2_gkGroup b E (Algebra.adjoin ℚ {J}) J d) :=
  g2k_gkGroup_isConnected_adjoin_of_isAlt b E J hd hJ hE hAlt hskew

theorem g2_hodgeLieIsGk_of_eq_aux (b : Module.Basis (Fin n) ℚ V)
    (E : LinearMap.BilinForm ℚ V) (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V)
    {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V))
    (h : g2_hodgeGroup H hH b = g2_gkGroup b E R J d) : HodgeLieIsGk H hH E R J := by
  have hlie := congrArg g1_lieOfSet h
  rw [g2_lie_hodgeGroup_aux H hH b, g2_lie_gkGroup_aux b E R J hd hJ] at hlie
  exact Submodule.map_injective_of_injective
    (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
      (Algebra.TensorProduct.basis ℂ b)).injective hlie

theorem g2_eq_of_hodgeLieIsGk_aux (b : Module.Basis (Fin n) ℚ V)
    (E : LinearMap.BilinForm ℚ V) (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V)
    {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V))
    (hconn : @IsConnected _ (g1_zariski ℂ n) (g2_gkGroup b E R J d))
    (h : HodgeLieIsGk H hH E R J) : g2_hodgeGroup H hH b = g2_gkGroup b E R J d := by
  have hHg := g2_isRatAlgSubgroup_hodgeGroup_aux H hH b
  have hGk := g2_isRatAlgSubgroup_gkGroup_aux b E R J hd hJ
  have heq := g1_eq_of_lie_eq (g2b_algGroup hHg) (g2b_algGroup hGk)
    (g2_hodgeGroup_isConnected_aux H hH b) hconn (by
      change g1_lieOfSet (g2_hodgeGroup H hH b) = g1_lieOfSet (g2_gkGroup b E R J d)
      rw [g2_lie_hodgeGroup_aux H hH b, g2_lie_gkGroup_aux b E R J hd hJ]
      exact congrArg _ h)
  exact congrArg (fun G : Subgroup _ => (G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))) heq

end General

section Rotation

theorem g2_hodgeGroup_rotation_aux :
    g2_hodgeGroup (complexStructureHodge rotation 1 0)
        (isInternal_complexStructureHodge rotation_mul_rotation (by decide))
        (Pi.basisFun ℚ (Fin 2)) =
      {g : Matrix.GeneralLinearGroup (Fin 2) ℂ | (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
        (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ∧
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ∧
        (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1} :=
  g2b_hodgeGroup_rotation _

theorem g2_not_isRatAlgSubgroup_circleImage_rotation_aux :
    ¬ g2_IsRatAlgSubgroup (g2_circleImage (complexStructureHodge rotation 1 0)
        (isInternal_complexStructureHodge rotation_mul_rotation (by decide))
        (Pi.basisFun ℚ (Fin 2))) :=
  g2b_not_isRatAlgSubgroup_circleImage _

theorem g2_gkGroup_rotation_aux :
    g2_gkGroup (Pi.basisFun ℚ (Fin 2)) (Matrix.toBilin' !![0, 1; -1, 0])
        (Algebra.adjoin ℚ {rotation}) rotation 1 = {1} :=
  g2b_gkGroup_rotation

end Rotation

section PW

open CategoryTheory AlgebraicGeometry HodgeLean.RealDefs HodgeLean.Adapters
open scoped CategoryTheory.MonObj

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom] {L : Type*} [Field L] [Algebra ℚ L]

theorem g2_pw_hodgeLieIsGk_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (E : LinearMap.BilinForm ℚ (HQ A 1))
    (hHg : letI := (finiteBetti_abelian A).finite 1
      g2_HodgeGroupEqGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal E (pwActionRange A θ) (pwAction A θ u) d) :
    letI := (finiteBetti_abelian A).finite 1
    HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
      (abelianWeightOneHodgeStructure A).isInternal E (pwActionRange A θ) (pwAction A θ u) := by
  have := (finiteBetti_abelian A).finite 1
  refine g2_hodgeLieIsGk_of_eq_aux _ _ (Module.finBasis ℚ (HQ A 1)) E _ _ hd ?_ hHg
  rw [← map_mul, ← pow_two, hu, map_neg, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    neg_smul]

end PW

end HodgeLean.Foundations

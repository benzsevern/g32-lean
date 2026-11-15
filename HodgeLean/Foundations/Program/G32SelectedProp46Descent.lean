import HodgeLean.Foundations.Program.G32PropFourSixDefs
import HodgeLean.Blocks.Weil.WeilTheoremHodge

noncomputable section
open scoped TensorProduct
open HodgeBlocks HodgeBlocks.WeilAction

namespace HodgeLean.Foundations.Program

theorem g32h46_exterior_symm_ιMulti {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (n : ℕ) (v : Fin n → ℂ ⊗[ℚ] V) :
    (exteriorPowerBaseChangeEquiv n).symm (exteriorPower.ιMulti ℂ n v) =
      (tensorPowerToExteriorPower V n).baseChange ℂ
        ((tensorPowerBaseChange V n).symm (PiTensorProduct.tprod ℂ v)) := by
  apply (exteriorPowerBaseChangeEquiv n).injective
  rw [LinearEquiv.apply_symm_apply,
    exteriorPowerBaseChangeEquiv_baseChange_tensorPowerToExteriorPower,
    LinearEquiv.apply_symm_apply, tensorPowerToExteriorPowerComplex_tprod]

theorem g32h46_exterior_sigma_ιMulti {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (n : ℕ) (v : Fin n → ℂ ⊗[ℚ] V) :
    sigmaQ (⋀[ℚ]^n V)
        ((exteriorPowerBaseChangeEquiv n).symm (exteriorPower.ιMulti ℂ n v)) =
      (exteriorPowerBaseChangeEquiv n).symm
        (exteriorPower.ιMulti ℂ n (fun i => sigmaQ V (v i))) := by
  rw [g32h46_exterior_symm_ιMulti, sigmaQ_baseChange,
    sigma_tensorPowerBaseChange_symm, tensorPowerSigma_tprod,
    g32h46_exterior_symm_ιMulti]

theorem g32h46_sigma_mem_baseChange {V : Type*} [AddCommGroup V] [Module ℚ V]
    (Q : Submodule ℚ V) {x : ℂ ⊗[ℚ] V} (hx : x ∈ Q.baseChange ℂ) :
    sigmaQ V x ∈ Q.baseChange ℂ := by
  rw [Submodule.baseChange_eq_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    change sigmaQR V ((1 : ℂ) ⊗ₜ[ℚ] v) ∈ _
    rw [sigmaQ_tmul, show (starRingEnd ℂ) 1 = 1 from map_one _]
    apply Submodule.subset_span
    exact ⟨v, hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy hx' hy' => rw [map_add]; exact Submodule.add_mem _ hx' hy'
  | smul c x hx hx' => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx'

end HodgeLean.Foundations.Program

namespace HodgeLean.Foundations.Program
open HodgeBlocks HodgeBlocks.WeilAction

theorem g32h46_exterior_sigma_range {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (n : ℕ) (S T : Submodule ℂ (ℂ ⊗[ℚ] V))
    (hST : ∀ x ∈ S, sigmaQ V x ∈ T) (x : ⋀[ℂ]^n S) :
    sigmaQ (⋀[ℚ]^n V) ((exteriorPowerBaseChangeEquiv n).symm
      (exteriorPower.map n S.subtype x)) ∈
        (LinearMap.range (exteriorPower.map n T.subtype)).map
          (exteriorPowerBaseChangeEquiv n).symm.toLinearMap := by
  classical
  have hx : x ∈ Submodule.span ℂ (Set.range (exteriorPower.ιMulti ℂ n)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [exteriorPower.map_apply_ιMulti, g32h46_exterior_sigma_ιMulti]
    refine ⟨exteriorPower.ιMulti ℂ n (fun i => sigmaQ V (v i : ℂ ⊗[ℚ] V)), ?_, rfl⟩
    refine ⟨exteriorPower.ιMulti ℂ n (fun i => (⟨_, hST _ (v i).property⟩ : T)), ?_⟩
    rw [exteriorPower.map_apply_ιMulti]
    rfl
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy hx' hy' =>
    simp only [map_add]
    exact Submodule.add_mem _ hx' hy'
  | smul c x hx hx' =>
    simp only [map_smul, map_smulₛₗ]
    exact Submodule.smul_mem _ _ hx'

theorem g32h46_conjugate_wedge_image_le {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] [AddCommGroup W] [Module ℚ W] (n : ℕ)
    (f : (⋀[ℚ]^n V) →ₗ[ℚ] W) (S T : Submodule ℂ (ℂ ⊗[ℚ] V))
    (hTS : ∀ x ∈ T, sigmaQ V x ∈ S) (Q : Submodule ℚ W)
    (hS : (LinearMap.range (exteriorPower.map n S.subtype)).map
      (f.baseChange ℂ ∘ₗ (exteriorPowerBaseChangeEquiv n).symm.toLinearMap) ≤ Q.baseChange ℂ) :
    (LinearMap.range (exteriorPower.map n T.subtype)).map
      (f.baseChange ℂ ∘ₗ (exteriorPowerBaseChangeEquiv n).symm.toLinearMap) ≤ Q.baseChange ℂ := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  obtain ⟨y, hy, he⟩ := g32h46_exterior_sigma_range n T S hTS x
  have hz := hS (Submodule.mem_map_of_mem hy)
  change f.baseChange ℂ ((exteriorPowerBaseChangeEquiv n).symm y) ∈ _ at hz
  change (exteriorPowerBaseChangeEquiv n).symm y = _ at he
  rw [he, ← sigmaQ_baseChange] at hz
  have hz' := g32h46_sigma_mem_baseChange Q hz
  rw [sigmaQ_involutive] at hz'
  exact hz'

theorem g32h46_rational_wedge_image_le {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] [AddCommGroup W] [Module ℚ W] (n : ℕ)
    (f : (⋀[ℚ]^n V) →ₗ[ℚ] W) (P : Submodule ℚ (⋀[ℚ]^n V))
    (S T : Submodule ℂ (ℂ ⊗[ℚ] V)) (Q : Submodule ℚ W)
    (hP : ∀ w ∈ P, complexifyWedge n w ∈
      LinearMap.range (exteriorPower.map n S.subtype) ⊔
        LinearMap.range (exteriorPower.map n T.subtype))
    (hS : (LinearMap.range (exteriorPower.map n S.subtype)).map
      (f.baseChange ℂ ∘ₗ (exteriorPowerBaseChangeEquiv n).symm.toLinearMap) ≤ Q.baseChange ℂ)
    (hT : (LinearMap.range (exteriorPower.map n T.subtype)).map
      (f.baseChange ℂ ∘ₗ (exteriorPowerBaseChangeEquiv n).symm.toLinearMap) ≤ Q.baseChange ℂ) :
    P.map f ≤ Q := by
  apply (Submodule.baseChange_le_iff (A := ℂ)).mp
  rw [Submodule.baseChange_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have hboth :
      (LinearMap.range (exteriorPower.map n S.subtype) ⊔
        LinearMap.range (exteriorPower.map n T.subtype)).map
        (f.baseChange ℂ ∘ₗ (exteriorPowerBaseChangeEquiv n).symm.toLinearMap) ≤
          Q.baseChange ℂ := by
    rw [Submodule.map_sup]
    exact sup_le hS hT
  have hz := hboth (Submodule.mem_map_of_mem (hP w hw))
  change f.baseChange ℂ ((exteriorPowerBaseChangeEquiv n).symm
    (complexifyWedge n w)) ∈ _ at hz
  rw [← exteriorPowerBaseChangeEquiv_tmul, LinearEquiv.symm_apply_apply,
    LinearMap.baseChange_tmul] at hz
  exact hz

end HodgeLean.Foundations.Program

noncomputable section

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

theorem g32h46_wedgeClasses_cast (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Submodule ℂ (ℂ ⊗[ℚ] HQ X 1)) (n n' : ℕ) (hn : n = n') :
    letI := (torusCohomology_cupProductOf X).finite
    (LinearMap.range (exteriorPower.map n S.subtype)).map
      ((((HQ.castEquiv X hn).toLinearMap ∘ₗ (cupProductOf X).cupWedgeMap n).baseChange ℂ) ∘ₗ
        (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv n).symm.toLinearMap) =
      g32p_wedgeClasses X S n' := by
  subst n'
  rfl

theorem g32h46_weilAlg_of_line_aux (P : g32t_Sixfold) (p : ℕ) (hp : g32h_h10 P = p)
    (hL : letI := (torusCohomology_cupProductOf P.X).finite
      g32p_wedgeClasses P.X P.W.Vs (2 * p) ≤ (algebraicCycleClassSpan P.X p).baseChange ℂ) :
    g32t_WeilAlg P := by
  subst p
  letI := (torusCohomology_cupProductOf P.X).finite
  intro hW
  let k := g32h_h10 P
  change (P.W.weilClasses
    (h10_sup_h01_eq_top (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
      (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X)) hW).map
      ((HQ.castEquiv P.X (two_mul k).symm).toLinearMap ∘ₗ
        (cupProductOf P.X).cupWedgeMap (k + k)) ≤ algebraicCycleClassSpan P.X k
  let f : (⋀[ℚ]^(k + k) (HQ P.X 1)) →ₗ[ℚ] HQ P.X (2 * k) :=
    (HQ.castEquiv P.X (two_mul k).symm).toLinearMap ∘ₗ
      (cupProductOf P.X).cupWedgeMap (k + k)
  have hS : (LinearMap.range (exteriorPower.map (k + k) P.W.Vs.subtype)).map
      (f.baseChange ℂ ∘ₗ
        (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (k + k)).symm.toLinearMap) ≤
          (algebraicCycleClassSpan P.X k).baseChange ℂ := by
    rw [show f = (HQ.castEquiv P.X (two_mul k).symm).toLinearMap ∘ₗ
      (cupProductOf P.X).cupWedgeMap (k + k) from rfl,
      g32h46_wedgeClasses_cast]
    exact hL
  have hbar : ∀ x ∈ P.W.Vsbar, HodgeBlocks.sigmaQ (HQ P.X 1) x ∈ P.W.Vs := by
    intro x hx
    rw [← P.W.map_Vs_sigmaQ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change HodgeBlocks.sigmaQ (HQ P.X 1) (HodgeBlocks.sigmaQ (HQ P.X 1) y) ∈ _
    rw [HodgeBlocks.sigmaQ_involutive]
    exact hy
  exact g32h46_rational_wedge_image_le (k + k) f _ P.W.Vs P.W.Vsbar
    (algebraicCycleClassSpan P.X k) (fun _ hw => hw) hS
      (g32h46_conjugate_wedge_image_le (k + k) f P.W.Vs P.W.Vsbar hbar
        (algebraicCycleClassSpan P.X k) hS)

end HodgeLean.Foundations.Program

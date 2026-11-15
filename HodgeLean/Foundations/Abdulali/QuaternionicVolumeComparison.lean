import HodgeLean.Foundations.Abdulali.SelectedEigenspaces
import HodgeLean.Foundations.Abdulali.ComplexCup
import HodgeLean.Foundations.Abdulali.ExteriorPolynomialSpan
import HodgeLean.Foundations.Program.MilneScalarDescent
import HodgeLean.Adapters.F1575
import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitRankBounds
import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitTransport

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program.TypeIIIPaper
namespace HodgeLean.Foundations.Abdulali

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

local instance : Module.Finite ℚ (HQ A 1) :=
  (torusCohomology_cupProductOf A).finite


/-- Membership in a complexified cohomology subspace commutes with a cast of
the codimension index.
Source: scalar extension of the canonical equality transport. -/
theorem degree_cast_baseChange_mem {i j : ℕ} (h : i = j)
    (U : Submodule ℚ (HQ A (2 * i))) (u : ℂ ⊗[ℚ] HQ A (2 * j)) :
    u ∈ (cast (congrArg (fun n => Submodule ℚ (HQ A (2*n))) h) U).baseChange ℂ ↔
      (HQ.castEquiv A (congrArg (2*·) h.symm)).toLinearMap.baseChange ℂ u ∈
        U.baseChange ℂ := by
  subst j
  change u ∈ U.baseChange ℂ ↔ (LinearMap.id.baseChange ℂ) u ∈ U.baseChange ℂ
  rw [LinearMap.baseChange_id, LinearMap.id_apply]

variable
  (W : letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)
  (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)

/-- The base determinant line in the fixed split identification lies in the
complexification of the selected rational quaternionic degree-six space.
The action equation fixes the identification, and the diagonal Eisenstein
matrix fixes the selected quadratic subfield.
Source: van Geemen–Verra, Quaternionic Pryms and Hodge Classes, §4.6,
Proposition 4.7; Abdulali, Annals of Mathematics 155 (2002), §3. -/
theorem quaternionic_base_volume_aux (P : GeneralPELMember A W pol hM)
    (s : ℂ) (hs : s ^ 2 = -3)
    (a : ℍ[ℂ, -3, 0, (P.b : ℂ)] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (hI : a ⟨0, 1, 0, 0⟩ = !![s, 0; 0, -s])
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1))
    (he : ∀ q z, quaternionComplexAction P.b (typeIIIQuaternionAction A W pol hM P) q (e z) =
      e ((Matrix.toLin' (a q)).rTensor (Fin 6 → ℂ) z)) :
    complexCupEquiv A 6 (exteriorPower.ιMulti ℂ 6 (fun i =>
      e ((Pi.single 0 1 : Fin 2 → ℂ) ⊗ₜ[ℂ] (Pi.basisFun ℂ (Fin 6) i)))) ∈
      (quaternionicSpan A (weilSix A W pol hM)).baseChange ℂ := by
  classical
  let z (i : Fin 6) := (Pi.single 0 1 : Fin 2 → ℂ) ⊗ₜ[ℂ] (Pi.basisFun ℂ (Fin 6) i)
  let v := exteriorPower.ιMulti ℂ 6 (fun i => e (z i))
  have hmatrix : Matrix.toLin' (a ⟨0, 1, 0, 0⟩) (Pi.single 0 1) =
      s • (Pi.single 0 1 : Fin 2 → ℂ) := by
    rw [hI]
    ext k
    fin_cases k <;> simp [Matrix.toLin'_apply, Matrix.mulVec, Fin.sum_univ_two,
      Pi.single_apply]
  have hvec (i : Fin 6) :
      -((Matrix.toLin' (a ⟨0, 1, 0, 0⟩)).rTensor (Fin 6 → ℂ) (z i)) = (-s) • z i := by
    dsimp only [z]
    rw [LinearMap.rTensor_tmul, hmatrix, ← TensorProduct.smul_tmul', neg_smul]
  have hsign : -s = HodgeBlocks.WeilAction.omegaC 3 ∨
      -s = -HodgeBlocks.WeilAction.omegaC 3 := by
    apply (sq_eq_sq_iff_eq_or_eq_neg).mp
    rw [neg_sq, hs, HodgeBlocks.WeilAction.omegaC_sq (by norm_num : (0 : ℚ) < 3)]
    norm_num
  have htop : v ∈ LinearMap.range (exteriorPower.map 6 W.Vs.subtype) ⊔
      LinearMap.range (exteriorPower.map 6 W.Vsbar.subtype) := by
    rcases hsign with hp | hp
    · have hz (i : Fin 6) : e (z i) ∈ W.Vs := by
        apply (typeIII_selected_eigenspaces A W pol hM P a e he (z i)).1.mpr
        rw [hvec, hp]
      apply Submodule.mem_sup_left
      refine ⟨exteriorPower.ιMulti ℂ 6 (fun i => ⟨e (z i), hz i⟩), ?_⟩
      rw [exteriorPower.map_apply_ιMulti]
      rfl
    · have hz (i : Fin 6) : e (z i) ∈ W.Vsbar := by
        apply (typeIII_selected_eigenspaces A W pol hM P a e he (z i)).2.mpr
        rw [hvec, hp]
      apply Submodule.mem_sup_right
      refine ⟨exteriorPower.ιMulti ℂ 6 (fun i => ⟨e (z i), hz i⟩), ?_⟩
      rw [exteriorPower.map_apply_ιMulti]
      rfl
  have hn : 6 = Module.finrank ℂ ↥(W.Vs ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.H (1, 0)) +
      Module.finrank ℂ ↥(W.Vs ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1.H (1, 0)) := by
    rw [hM.finrank_eq_three]
  have ht := f1575_topLines_mem_weil hM hn v htop
  apply Submodule.baseChange_mono ℂ (le_quaternionicSpan A _) ?_
  change complexCupEquiv A 6 v ∈ (cast (congrArg
    (fun n => Submodule ℚ (HQ A (2*n))) hM.finrank_eq_three)
    (weilClassOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      hM.isWeilType)).baseChange ℂ
  rw [degree_cast_baseChange_mem A hM.finrank_eq_three]
  have hc : complexCupEquiv A 6 =
      f1575ExteriorCohomology (torusCohomology_cupProductOf A) 6 := by
    rfl
  rw [hc]
  exact ht


variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}

/-- Scalar extension of the homogeneous rational sum-pullback family.
This statement applies to every rational input subspace, and does not assert
any invariant generation or Hodge-conjecture conclusion. Conjugation in the
covariant quaternion action accounts for the opposite endomorphism action.
Source: Weyl, The Classical Groups, Chapter II, §9 (polarization);
Mumford, Abelian Varieties, §19 (rational endomorphisms and denominators);
Abdulali, Annals of Mathematics 155 (2002), Remark 4.2. -/
theorem quaternionic_complex_sum_pullback_aux (P : GeneralPELMember A W pol hM)
    (power : AbelianPowerData A Y r) (n : ℕ) (U : Submodule ℚ (HQ A n))
    (q : Fin r → ℍ[ℂ, -3, 0, (P.b : ℂ)])
    (u : ℂ ⊗[ℚ] HQ A n) (hu : u ∈ U.baseChange ℂ) :
    complexCupEquiv Y n (exteriorPower.map n
      (∑ i, (homPullback (power.proj i) 1).baseChange ℂ ∘ₗ
        quaternionComplexAction P.b (typeIIIQuaternionAction A W pol hM P) (q i))
      ((complexCupEquiv A n).symm u)) ∈
      (⨆ f : Fin r → AbelianEnd A,
        U.map (homPullback (power.sumMap f) n)).baseChange ℂ := by
  classical
  let L (i : Fin r) : (Fin (r * 4) → ℂ) →ₗ[ℂ] ℍ[ℂ, -3, 0, (P.b : ℂ)] :=
    (QuaternionAlgebra.linearEquivTuple (-3 : ℂ) 0 (P.b : ℂ)).symm.toLinearMap ∘ₗ
      LinearMap.funLeft ℂ ℂ (fun k : Fin 4 => finProdFinEquiv (i, k))
  let F : (Fin (r * 4) → ℂ) →ₗ[ℂ]
      ((ℂ ⊗[ℚ] HQ A 1) →ₗ[ℂ] (ℂ ⊗[ℚ] HQ Y 1)) :=
    { toFun := fun x => ∑ i, (homPullback (power.proj i) 1).baseChange ℂ ∘ₗ
        quaternionComplexAction P.b (typeIIIQuaternionAction A W pol hM P) (L i x)
      map_add' := by
        intro x y
        simp only [map_add, LinearMap.comp_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [map_smul, LinearMap.comp_smul, Finset.smul_sum, RingHom.id_apply] }
  let x : Fin (r * 4) → ℂ := fun j =>
    QuaternionAlgebra.equivTuple (-3 : ℂ) 0 (P.b : ℂ)
      (q (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2
  have hx (i : Fin r) : L i x = q i := by
    change (QuaternionAlgebra.linearEquivTuple (-3 : ℂ) 0 (P.b : ℂ)).symm
      (fun k => x (finProdFinEquiv (i, k))) = q i
    simp only [x, Equiv.symm_apply_apply]
    exact (QuaternionAlgebra.linearEquivTuple (-3 : ℂ) 0 (P.b : ℂ)).symm_apply_apply _
  have hF : F x = ∑ i, (homPullback (power.proj i) 1).baseChange ℂ ∘ₗ
      quaternionComplexAction P.b (typeIIIQuaternionAction A W pol hM P) (q i) := by
    change (∑ i : Fin r, (homPullback (power.proj i) 1).baseChange ℂ ∘ₗ
      quaternionComplexAction P.b (typeIIIQuaternionAction A W pol hM P) (L i x)) = _
    simp only [hx]
  rw [← hF]
  have hp := Submodule.mem_map_of_mem (f := (complexCupEquiv Y n).toLinearMap)
    (exterior_map_mem_span_rational_parameters F ((complexCupEquiv A n).symm u) x)
  rw [Submodule.map_span] at hp
  apply (Submodule.span_le.mpr ?_) hp
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  let qr (i : Fin r) : ℍ[ℚ, -3, 0, P.b] :=
    (QuaternionAlgebra.linearEquivTuple (-3 : ℚ) 0 P.b).symm
      (fun k => b (finProdFinEquiv (i, k)))
  let d (i : Fin r) : AbelianEnd0 A := P.end0 (star (qr i))
  let fQ : HQ A 1 →ₗ[ℚ] HQ Y 1 :=
    ∑ i, homPullback (power.proj i) 1 ∘ₗ (abelianEnd0Action A (d i)).unop
  have hL (i : Fin r) : L i (fun j => (b j : ℂ)) = quaternionRationalInclusion P.b (qr i) := by
    ext <;> simp [L, qr, LinearMap.funLeft, quaternionRationalInclusion,
      QuaternionAlgebra.coe_linearEquivTuple_symm, QuaternionAlgebra.equivTuple]
  have hRat : F (fun i => (b i : ℂ)) = fQ.baseChange ℂ := by
    change (∑ i : Fin r, (homPullback (power.proj i) 1).baseChange ℂ ∘ₗ
      quaternionComplexAction P.b (typeIIIQuaternionAction A W pol hM P)
        (L i (fun j => (b j : ℂ)))) =
      (LinearMap.baseChangeHom ℚ ℂ (HQ A 1) (HQ Y 1)) fQ
    simp only [fQ, map_sum, hL, quaternionComplexAction_rational,
      LinearMap.baseChangeHom_apply, LinearMap.baseChange_comp]
    rfl
  change complexCupEquiv Y n
    (exteriorPower.map n (F (fun i => (b i : ℂ))) ((complexCupEquiv A n).symm u)) ∈ _
  rw [hRat, complexCupEquiv_naturality A Y n fQ u]
  change (rationalPowerPullback power d n).baseChange ℂ u ∈ _
  have hm := Submodule.mem_map_of_mem
    (f := (rationalPowerPullback power d n).baseChange ℂ) hu
  rw [HodgeLean.Foundations.Program.m2_map_baseChange] at hm
  apply Submodule.baseChange_mono ℂ ?_ hm
  rw [← rationalPowerPullback_span_eq power n U]
  exact le_iSup (fun d => U.map (rationalPowerPullback power d n)) d


end HodgeLean.Foundations.Abdulali

import HodgeLean.Foundations.Program.SchoenCycleS3
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection

theorem projective_model_dim (P : Over (Spec ↧ℂ)) [IsIntegral P.left] (k : ℕ)
    (e : P ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    dim P.left = k := by
  unfold TopologicalSpace.dim
  rw [e.hom.left.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact s0_complex_projective_dimension k

theorem generic_avoidance_of_lower_dim_section
    (P : Over (Spec ↧ℂ)) [IsIntegral P.left] (k : ℕ) (hk : 0 < k)
    (e : P ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (I : P.left.IdealSheafData)
    (eI : s2c_subscheme P I ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ)))
    (x : P.left) (hx : IsGenericPoint x Set.univ) : x ∉ I.support := by
  intro hm
  have hs : I.support = ⊤ := by
    apply top_le_iff.mp
    intro y _
    exact (hx.mem_closed_set_iff I.support.isClosed).mp hm (Set.mem_univ y)
  have hI : I = ⊥ := Scheme.IdealSheafData.support_eq_top_iff.mp hs
  haveI : IsIso I.subschemeι := by rw [hI]; infer_instance
  haveI : IsIntegral I.subscheme := IsIntegral.of_isIso (inv I.subschemeι)
  haveI : IsIntegral (s2c_subscheme P I).left := by
    change IsIntegral I.subscheme
    infer_instance
  have hd : dim (s2c_subscheme P I).left = dim P.left := by
    change dim I.subscheme = dim P.left
    unfold TopologicalSpace.dim
    rw [I.subschemeι.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  rw [projective_model_dim _ _ eI, projective_model_dim _ _ e] at hd
  omega

theorem paired_generic_avoidance
    (P : Over (Spec ↧ℂ)) [IsIntegral P.left] (k r : ℕ) (hk : 0 < k)
    (e : P ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (B : Scheme) (ℓ : P.left ⟶ B) (D : Fin (2 * r) → B.IdealSheafData)
    (hpair : ∀ i : Fin r,
      (D ⟨2 * i.val, by omega⟩).comap ℓ = (D ⟨2 * i.val + 1, by omega⟩).comap ℓ)
    (hsingle : ∀ i : Fin r, Nonempty (s2c_subscheme P
      ((D ⟨2 * i.val, by omega⟩).comap ℓ) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ)))) :
    ∀ t : Fin (2 * r), ∀ x : P.left, IsGenericPoint x Set.univ → ℓ x ∉ (D t).support := by
  intro t x hx hm
  let i : Fin r := ⟨t.val / 2, by omega⟩
  obtain ⟨eI⟩ := hsingle i
  have hn := generic_avoidance_of_lower_dim_section P k hk e _ eI x hx
  apply hn
  have ht : t = ⟨2 * i.val, by omega⟩ ∨ t = ⟨2 * i.val + 1, by omega⟩ := by
    dsimp only [i]
    have htval : t.val = 2 * (t.val / 2) ∨ t.val = 2 * (t.val / 2) + 1 := by omega
    exact htval.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
  rcases ht with ht | ht
  · rw [ht] at hm
    rw [Scheme.IdealSheafData.support_comap]
    exact hm
  · rw [ht] at hm
    rw [hpair i]
    rw [Scheme.IdealSheafData.support_comap]
    exact hm

end HodgeLean.WitnessSelection

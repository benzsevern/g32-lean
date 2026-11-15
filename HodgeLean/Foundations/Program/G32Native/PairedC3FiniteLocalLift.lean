import HodgeLean.Ported.NYLL.SchemeTheory.Modules.LocalMorphisms

/-! # Simultaneous local lifting of finite section families -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native

/-- Every finite family of sections lifts on a common neighborhood through
an epimorphism of native module sheaves, without quasicoherence assumptions. -/
theorem paired_c3_finite_local_lift {X : Scheme} {M N : X.Modules}
    (g : M ⟶ N) [Epi g] {I : Type} [Finite I]
    (U : X.Opens) (z : I → Γ(N, U)) (x : X) (hx : x ∈ U) :
    ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧
      ∃ t : I → Γ(M, W), ∀ i,
        g.app W (t i) = N.presheaf.map (homOfLE hWU).op (z i) := by
  have hlocal := (Scheme.Modules.Hom.epi_iff_locallySurjective g).mp inferInstance
  choose V hVU hxV t ht using (fun i => hlocal U (z i) x hx)
  let W : X.Opens := U ⊓ ⨅ i, V i
  have hWU : W ≤ U := inf_le_left
  have hWV (i : I) : W ≤ V i := inf_le_right.trans (iInf_le V i)
  have hxW : x ∈ W := by
    refine ⟨hx, ?_⟩
    change x ∈ ((⨅ i, V i : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxV
  refine ⟨W, hWU, hxW, (fun i => M.presheaf.map (homOfLE (hWV i)).op (t i)), ?_⟩
  intro i
  have hn := ConcreteCategory.congr_hom
    (g.mapPresheaf.naturality (homOfLE (hWV i)).op) (t i)
  change g.app W (M.presheaf.map (homOfLE (hWV i)).op (t i)) =
    N.presheaf.map (homOfLE (hWV i)).op (g.app (V i) (t i)) at hn
  rw [hn, ht i]
  exact (ConcreteCategory.congr_hom
    (N.presheaf.map_comp (homOfLE (hVU i)).op (homOfLE (hWV i)).op) (z i)).symm

#print axioms paired_c3_finite_local_lift
end HodgeLean.Foundations.Program.G32Native

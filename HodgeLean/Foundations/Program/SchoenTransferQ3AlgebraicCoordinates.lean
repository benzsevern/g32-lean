import HodgeLean.Foundations.Program.SchoenTransferQ3TangentialCharts

/-! Algebraic agreement of the ambient lifts with the actual etale coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Ambient coordinate lifts agree as regular sections with the specified
etale support coordinates on one common Zariski neighbourhood. -/
theorem s4_q3_support_coordinates_algebraic_agreement
    {D W : Over (Spec ↧ℂ)} (r : ℕ) [SmoothOfRelativeDimension r D.hom]
    (j : D ⟶ W) [IsClosedImmersion j.left] (x : D.left) :
    let E := AlgebraicGeometry.localEtaleCoordinates D r x
    ∃ (U : W.left.Opens) (_ : IsAffineOpen U) (hxU : j.left x ∈ U)
      (g : Fin r → Γ(W.left, U)) (V : D.left.Opens) (_ : x ∈ V)
      (hVU : V ≤ j.left ⁻¹ᵁ U) (hVE : V ≤ E.neighborhood),
      ∀ i, D.left.presheaf.map (homOfLE hVU).op (j.left.app U (g i)) =
        D.left.presheaf.map (homOfLE hVE).op (E.coordinateAlgHom (MvPolynomial.X i)) := by
  classical
  let E := AlgebraicGeometry.localEtaleCoordinates D r x
  have hxE : x ∈ E.neighborhood := E.mem
  obtain ⟨U, hU, hxU, g, hg⟩ := a3b4g_closed_immersion_affine_germ_lifts_core
    j.left x r (fun i => D.left.presheaf.germ E.neighborhood x hxE
      (E.coordinateAlgHom (MvPolynomial.X i)))
  have hnear (i : Fin r) := TopCat.Presheaf.germ_eq D.left.presheaf x hxU hxE
    (j.left.app U (g i)) (E.coordinateAlgHom (MvPolynomial.X i))
    ((Scheme.Hom.germ_stalkMap_apply j.left U x hxU (g i)).symm.trans (hg i))
  choose A hxA aU aE ha using hnear
  let V : D.left.Opens := (j.left ⁻¹ᵁ U) ⊓ E.neighborhood ⊓ ⨅ i, A i
  have hVA (i : Fin r) : V ≤ A i := inf_le_right.trans (iInf_le A i)
  have hxV : x ∈ V := ⟨⟨hxU, hxE⟩, by
    change x ∈ ((⨅ i, A i : Opens D.left) : Set D.left)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxA⟩
  have hVU : V ≤ j.left ⁻¹ᵁ U := inf_le_left.trans inf_le_left
  have hVE : V ≤ E.neighborhood := inf_le_left.trans inf_le_right
  refine ⟨U, hU, hxU, g, V, hxV, hVU, hVE, ?_⟩
  intro i
  have hi := congrArg (D.left.presheaf.map (homOfLE (hVA i)).op) (ha i)
  have hres {P Q R : D.left.Opens} (b : P ⟶ Q) (c : Q ⟶ R) (s : Γ(D.left, R)) :
      D.left.presheaf.map b.op (D.left.presheaf.map c.op s) =
        D.left.presheaf.map (b ≫ c).op s := by
    exact (ConcreteCategory.congr_hom (D.left.presheaf.map_comp c.op b.op) s).symm
  rw [hres, hres] at hi
  exact hi

end HodgeLean.Foundations.Program

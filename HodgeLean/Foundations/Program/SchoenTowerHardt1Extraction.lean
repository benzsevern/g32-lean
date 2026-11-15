import HodgeLean.Foundations.Program.SchoenTowerHardt1Decomposition

/-! Component extraction from a finite Boolean preconnected cover. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A component is the finite union of the preconnected cover pieces meeting it.
Source: Coste, Real Algebraic Sets (2005), Proposition 1.6, finite union extraction step. -/
theorem s2v_hardt1_extract_component {n m : ℕ} (f : s2v_t11b_Formula n)
    (d : Fin m → s2v_t11b_Formula n)
    (hd : ∀ i, IsPreconnected (d i).realize ∧ (d i).realize ⊆ f.realize)
    (hcover : ∀ y ∈ f.realize, ∃ i, y ∈ (d i).realize) (x : f.realize) :
    ∃ c : s2v_t11b_Formula n, c.realize = Subtype.val '' connectedComponent x := by
  classical
  let I := {i : Fin m | ∃ y : f.realize, y ∈ connectedComponent x ∧ y.val ∈ (d i).realize}
  let E := Fintype.equivFin I
  obtain ⟨c, hc⟩ := s2v_t11b_finite_union_formula (fun q => d (E.symm q).val)
  refine ⟨c, ?_⟩
  ext y
  rw [hc]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨z, hz, hzd⟩ := (E.symm q).property
    let i := (E.symm q).val
    let F : (d i).realize → f.realize := fun t => ⟨t.val, (hd i).2 t.property⟩
    haveI : PreconnectedSpace (d i).realize := isPreconnected_iff_preconnectedSpace.mp (hd i).1
    have hF : Continuous F := continuous_subtype_val.subtype_mk _
    have hconn := isPreconnected_range hF
    have hzF : z ∈ Set.range F := ⟨⟨z.val, hzd⟩, Subtype.ext rfl⟩
    have hyF : (⟨y, (hd i).2 hq⟩ : f.realize) ∈ Set.range F := ⟨⟨y, hq⟩, rfl⟩
    refine ⟨⟨y, (hd i).2 hq⟩, ?_, rfl⟩
    have hmem := hconn.subset_connectedComponent hzF hyF
    rwa [← connectedComponent_eq hz] at hmem
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := hcover z.val z.property
    let j : I := ⟨i, z, hz, hi⟩
    refine ⟨E j, ?_⟩
    change z.val ∈ (d (E.symm (E j)).val).realize
    rwa [E.symm_apply_apply]

end HodgeLean.Foundations.Program

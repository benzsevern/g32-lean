import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPolyhedronFormula
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GraphImages

/-! The actual graph of a finite geometric triangulation supplies a compact Boolean target carrier. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_triangulated_carrier_formula {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hK : K.faces.Finite)
    (A : Set (EuclideanSpace ℝ (Fin m))) (h : K.space ≃ₜ A)
    (G : s2v_t11b_Formula (n + m))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (h x).val i)) :
    IsCompact A ∧ ∃ F : s2v_t11b_Formula m, F.realize = A := by
  have hcompact : IsCompact K.space :=
    hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp hcompact
  have himage : (fun x : K.space => (h x).val) '' Set.univ = A := by
    ext y
    exact ⟨fun ⟨x, _, he⟩ => he ▸ (h x).property,
      fun hy => ⟨h.symm ⟨y, hy⟩, trivial, congrArg Subtype.val (h.apply_symm_apply ⟨y, hy⟩)⟩⟩
  refine ⟨himage ▸ (isCompact_univ.image (continuous_subtype_val.comp h.continuous)), ?_⟩
  obtain ⟨P, hP⟩ := s2v_hardt6rb_complex_carrier_formula K hK
  obtain ⟨F, hF⟩ := s2v_hardt_cad5_relation_image_formula P G
  refine ⟨F, ?_⟩
  ext y
  rw [hF]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨a, _, ha⟩ := (hG _).mp hx
    have he : y = (h a).val := by
      ext i
      simpa only [PiLp.toLp_apply, Fin.append_right] using ha i
    exact he.symm ▸ (h a).property
  · intro hy
    let x := h.symm ⟨y, hy⟩
    refine ⟨⟨x.val, hP.symm ▸ x.property⟩, (hG _).mpr ⟨x, ?_, ?_⟩⟩
    · intro i
      simp only [PiLp.toLp_apply, Fin.append_left]
    · intro i
      simpa only [PiLp.toLp_apply, Fin.append_right, x] using
        (congrArg (fun z : A => z.val i) (h.apply_symm_apply ⟨y, hy⟩)).symm

end HodgeLean.Foundations.Program

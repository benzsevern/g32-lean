import HodgeLean.Foundations.Program.G32Native.ConormalLocalCodimension
import HodgeLean.Foundations.Program.G32Native.QuotientCodimensionParameters

/-! Adapt local parameters to a smooth closed subscheme of specified conormal rank. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program

/-- The given conormal frames determine how many local parameters generate the ideal. -/
theorem g32l4_conormal_frames_local_parameters
    (B : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (I : B.left.IdealSheafData) [Smooth (s2c_subscheme B I).hom] (r : ℕ)
    (hframe : ∀ x : I.subscheme, ∃ V : I.subscheme.Opens, x ∈ V ∧ Nonempty
      (Scheme.Modules.restrict (s2c_conormal I.subschemeι) V.ι ≅
        (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin r) : V.toScheme.Modules)))
    (x : B.left) (hx : x ∈ I.support) :
    ∃ (m : ℕ) (z : Fin m → B.left.presheaf.stalk x),
      r ≤ m ∧ IsRegularSystemOfParameters z ∧
      I.stalkIdeal x = Ideal.span (z '' {j | j.val < r}) := by
  obtain ⟨q, rfl⟩ := I.exists_subschemeι_eq hx
  letI : Smooth B.hom := SmoothOfRelativeDimension.smooth n B.hom
  letI : Smooth (I.subschemeι ≫ B.hom) :=
    inferInstanceAs (Smooth (s2c_subscheme B I).hom)
  letI : IsRegularLocalRing (B.left.presheaf.stalk (I.subschemeι q)) :=
    isRegularLocalRing_stalk B.hom (I.subschemeι q)
  letI : IsRegularLocalRing (B.left.presheaf.stalk (I.subschemeι q) ⧸
      I.stalkIdeal (I.subschemeι q)) :=
    isRegularLocalRing_quotient_stalkIdeal I B.hom hx
  exact g32l4_regular_quotient_parameters_of_codimension (I.stalkIdeal (I.subschemeι q)) r
    (g32l4_conormal_frames_local_codimension B n I r hframe q)

/-- Rank-one conormal frames give a local principal branch equation at every support point. -/
theorem g32l4_rank_one_conormal_local_equation
    (B : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (I : B.left.IdealSheafData) [Smooth (s2c_subscheme B I).hom]
    (hframe : ∀ x : I.subscheme, ∃ V : I.subscheme.Opens, x ∈ V ∧ Nonempty
      (Scheme.Modules.restrict (s2c_conormal I.subschemeι) V.ι ≅
        (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin 1) : V.toScheme.Modules)))
    (x : B.left) (hx : x ∈ I.support) :
    ∃ f : B.left.presheaf.stalk x,
      I.stalkIdeal x = Ideal.span {f} ∧ f ∈ maximalIdeal (B.left.presheaf.stalk x) := by
  obtain ⟨m, z, hrm, hz, hIz⟩ :=
    g32l4_conormal_frames_local_parameters B n I 1 hframe x hx
  let i : Fin m := ⟨0, by omega⟩
  have himage : z '' {j : Fin m | j.val < 1} = {z i} := by
    ext a
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hji : j = i := Fin.ext (by
        change j.val = 0
        change j.val < 1 at hj
        omega)
      rw [hji]
      exact Set.mem_singleton _
    · rintro rfl
      exact ⟨i, by change 0 < 1; omega, rfl⟩
  refine ⟨z i, ?_, ?_⟩
  · rw [himage] at hIz
    exact hIz
  · rw [← hz.1]
    exact Ideal.subset_span (Set.mem_range_self i)

end HodgeLean.Foundations.Program

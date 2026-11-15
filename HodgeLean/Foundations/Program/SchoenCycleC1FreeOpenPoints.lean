import HodgeLean.Foundations.Program.SchoenCycleC1FreePointHelpers

/-! # Free complex points in every nonempty open -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Every nonempty open of a smooth integral separated complex scheme
contains a complex point with a free orbit under a faithful finite action. -/
theorem s2e_c1_exists_free_complex_point_in_open
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsSeparated Y.hom]
    (G : Type) [Group G] [Finite G] (a : G → (Y ⟶ Y))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (V : Y.left.Opens)
    (hV : (V : Set Y.left).Nonempty) :
    ∃ z : ComplexPoint Y, z.underlying ∈ V ∧ Function.Injective (fun u => Point.map (a u) z) := by
  classical
  let A (u : G) : Set Y.left := Set.range (equalizer.ι (a u) (𝟙 Y)).left
  have hA (u : G) : IsClosed (A u) :=
    (equalizer.ι (a u) (𝟙 Y)).left.isClosedEmbedding.isClosed_range
  have hproper (u : G) (hu : u ≠ 1) : A u ≠ Set.univ := by
    intro hfull
    haveI : Surjective (equalizer.ι (a u) (𝟙 Y)).left := ⟨by
      intro x
      change x ∈ A u
      rw [hfull]
      trivial⟩
    haveI : IsIso (equalizer.ι (a u) (𝟙 Y)).left :=
      isIso_of_isClosedImmersion_of_surjective _
    apply hu
    apply hinj
    rw [ha1]
    apply Over.OverMorphism.ext
    rw [← cancel_epi (equalizer.ι (a u) (𝟙 Y)).left]
    exact congrArg Over.Hom.left (equalizer.condition (a u) (𝟙 Y))
  let U : Set Y.left := ⋂ u : G, {x | u = 1 ∨ x ∉ A u}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro u
    by_cases hu : u = 1
    · simp only [hu, true_or, Set.setOf_true]
      exact isOpen_univ
    · simpa only [hu, false_or, Set.compl_def] using (hA u).isOpen_compl
  have hgen : genericPoint Y.left ∈ U := by
    apply Set.mem_iInter.mpr
    intro u
    by_cases hu : u = 1
    · exact Or.inl hu
    · apply Or.inr
      have hne : (A u)ᶜ.Nonempty := Set.nonempty_compl.mpr (hproper u hu)
      exact ((genericPoint_spec Y.left).mem_open_set_iff (hA u).isOpen_compl).mpr (by simpa only [Set.univ_inter] using hne)
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hgV : genericPoint Y.left ∈ V :=
    ((genericPoint_spec Y.left).mem_open_set_iff V.isOpen).mpr (by
      simpa only [Set.univ_inter] using hV)
  obtain ⟨y, hyUV, hyc⟩ := nonempty_inter_closedPoints
    (show (U ∩ (V : Set Y.left)).Nonempty from ⟨genericPoint Y.left, hgen, hgV⟩)
    (hU.inter V.isOpen).isLocallyClosed
  have hy : y ∈ U := hyUV.1
  let z : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y hyc)
    (pointOfClosedPoint_comp Y.hom y hyc)
  have hz : z.underlying = y := pointOfClosedPoint_apply Y.hom y hyc _
  letI := s2e_quotientPointMulAction Y G a ha1 hamul
  refine ⟨z, hz ▸ hyUV.2, ?_⟩
  intro u v huv
  have he : u • z = v • z := huv
  have hfixed : (v⁻¹ * u) • z = z := by rw [mul_smul, he, inv_smul_smul]
  have hone : v⁻¹ * u = 1 := by
    by_contra hne
    have hnot : y ∉ A (v⁻¹ * u) :=
      (Set.mem_iInter.mp hy (v⁻¹ * u)).resolve_left hne
    have hfix : z ≫ a (v⁻¹ * u) = z ≫ 𝟙 Y := by
      exact hfixed.trans (Category.comp_id z).symm
    let t := equalizer.lift z hfix
    have ht : t ≫ equalizer.ι (a (v⁻¹ * u)) (𝟙 Y) = z := equalizer.lift_ι _ _
    apply hnot
    refine ⟨t.left (IsLocalRing.closedPoint ℂ), ?_⟩
    have ht' := congrArg (fun f => f.left (IsLocalRing.closedPoint ℂ)) ht
    exact ht'.trans hz
  calc
    u = v * (v⁻¹ * u) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    _ = v := by rw [hone, mul_one]

end HodgeLean.Foundations.Program

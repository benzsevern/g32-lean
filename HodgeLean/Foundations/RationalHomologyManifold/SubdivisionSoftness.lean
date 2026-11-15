import HodgeLean.Foundations.RationalHomologyManifold.CompactSubdivisionSections
import HodgeLean.Foundations.RationalHomologyManifold.FiniteAmbientSectionPatching
import HodgeLean.Foundations.DolbeaultCurve3Defs

/-! Compact support extension for the actual supported subdivision-limit sheaf.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Sections near closed supports extend by an actual finite-stage ambient chain on a smaller neighborhood.
Source: Bredon, Sheaf Theory, second edition, II.9 and VI.12; compact extension in the subdivided chain sheaf.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheaf_extend_by_ambient (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (n : ℕ) (K : Set X) (hK : IsClosed K) (U : Opens X) (hKU : K ⊆ U)
    (s : ((subdivisionLimitSheafComplex X).X n).obj.obj (Opposite.op U)) :
    ∃ (N : Opens X) (hNU : N ≤ U), K ⊆ N ∧
      ∃ (M : ℕ) (w : (SingularChainComplex ℚ X).X n),
        ((subdivisionLimitSheafComplex X).X n).obj.map (homOfLE (show N ≤ ⊤ from le_top)).op
          ((subdivisionAmbientSectionMap X n ⊤ M).hom w) =
        ((subdivisionLimitSheafComplex X).X n).obj.map (homOfLE hNU).op s := by
  classical
  let F := ((subdivisionLimitSheafComplex X).X n).obj
  obtain ⟨I, V, W, hV, M, z, hcover, hcl, hz⟩ :=
    subdivisionLimitSheaf_compact_shrunk_representatives X n K hK.isCompact U hKU s
  have hWiV (i : I) : W i ≤ V i := fun _ hx => hcl i (subset_closure hx)
  have hlocal (i : I) (O : Opens X) (hOi : O ≤ V i) :
      (subdivisionAmbientSectionMap X n O M).hom (z i) =
        F.map (homOfLE (hOi.trans (hV i))).op s := by
    have hr := ConcreteCategory.congr_hom
      (subdivisionAmbientSectionMap_restriction X n M (V i) O hOi) (z i)
    change F.map (homOfLE hOi).op ((subdivisionAmbientSectionMap X n (V i) M).hom (z i)) =
      (subdivisionAmbientSectionMap X n O M).hom (z i) at hr
    rw [hz i] at hr
    calc
      _ = F.map (homOfLE hOi).op (F.map (homOfLE (hV i)).op s) := hr.symm
      _ = _ := by
        rw [← ConcreteCategory.comp_apply, ← F.map_comp]
        rfl
  have hcompat (i j : I) :
      (subdivisionAmbientSectionMap X n (V i ⊓ V j) M).hom (z i) =
        (subdivisionAmbientSectionMap X n (V i ⊓ V j) M).hom (z j) :=
    (hlocal i _ inf_le_left).trans (hlocal j _ inf_le_right).symm
  obtain ⟨T, w, hw⟩ := finite_ambient_sections_patching X n M V W hcl z hcompat
  have hwsec (i : I) : (subdivisionAmbientSectionMap X n (W i) (M + T)).hom w =
      (subdivisionAmbientSectionMap X n (W i) (M + T)).hom
        ((rationalSubdivisionIterate X T).f n (z i)) := by
    exact congrArg (fun a =>
      ((toSheafify (Opens.grothendieckTopology X) ((subdivisionLimitPresheafComplex X).X n)).app
        (Opposite.op (W i)))
        ((((colimit.ι (presheafSubdivisionDiagram X) (M + T)).f n).app
          (Opposite.op (W i))) a)) (hw i)
  have hsect (i : I) : (subdivisionAmbientSectionMap X n (W i) (M + T)).hom w =
      F.map (homOfLE ((hWiV i).trans (hV i))).op s := by
    have ht := ConcreteCategory.congr_hom
      (subdivisionAmbientSectionMap_transition X n (W i) M T) (z i)
    change (subdivisionAmbientSectionMap X n (W i) (M + T)).hom
        ((rationalSubdivisionIterate X T).f n (z i)) =
      (subdivisionAmbientSectionMap X n (W i) M).hom (z i) at ht
    exact (hwsec i).trans (ht.trans (hlocal i _ (hWiV i)))
  let N : Opens X := ⨆ i : I, W i
  have hNU : N ≤ U := iSup_le (fun i => (hWiV i).trans (hV i))
  have hKN : K ⊆ N := fun x hx => Opens.mem_iSup.mpr (hcover x hx)
  let t := (subdivisionAmbientSectionMap X n ⊤ (M + T)).hom w
  refine ⟨N, hNU, hKN, M + T, w, ?_⟩
  change F.map (homOfLE (show N ≤ ⊤ from le_top)).op t = F.map (homOfLE hNU).op s
  apply TopCat.Presheaf.IsSheaf.section_ext
    (show TopCat.Presheaf.IsSheaf F from ((subdivisionLimitSheafComplex X).X n).property)
  intro x hx
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  refine ⟨W i, le_iSup W i, hxi, ?_⟩
  change F.map (homOfLE (le_iSup W i)).op
      (F.map (homOfLE (show N ≤ ⊤ from le_top)).op t) =
    F.map (homOfLE (le_iSup W i)).op (F.map (homOfLE hNU).op s)
  have htopmap : F.map (homOfLE (show N ≤ ⊤ from le_top)).op ≫
      F.map (homOfLE (le_iSup W i)).op =
        F.map (homOfLE (show W i ≤ ⊤ from le_top)).op := by
    rw [← F.map_comp]
    rfl
  have hUmap : F.map (homOfLE hNU).op ≫ F.map (homOfLE (le_iSup W i)).op =
      F.map (homOfLE ((hWiV i).trans (hV i))).op := by
    rw [← F.map_comp]
    rfl
  have htop := ConcreteCategory.congr_hom htopmap t
  have hUeq := ConcreteCategory.congr_hom hUmap s
  simp only [ConcreteCategory.comp_apply] at htop hUeq
  have hg := ConcreteCategory.congr_hom
    (subdivisionAmbientSectionMap_restriction X n (M + T) ⊤ (W i) le_top) w
  change F.map (homOfLE (show W i ≤ ⊤ from le_top)).op t =
    (subdivisionAmbientSectionMap X n (W i) (M + T)).hom w at hg
  exact htop.trans ((hg.trans (hsect i)).trans hUeq.symm)

#print axioms subdivisionLimitSheaf_extend_by_ambient

/-- Every term of the actual supported subdivision-limit chain sheaf is soft on a compact Hausdorff space.
Source: Bredon, Sheaf Theory, second edition, II.9 and VI.12; softness of the subdivided chain sheaf.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheaf_isSoft (X : TopCat.{0}) [CompactSpace X] [T2Space X] (n : ℕ) :
    IsSoft ((subdivisionLimitSheafComplex X).X n) := by
  intro K U hK hKU s
  obtain ⟨N, hNU, hKN, M, w, hw⟩ := subdivisionLimitSheaf_extend_by_ambient X n K hK U hKU s
  exact ⟨N, hNU, hKN, (subdivisionAmbientSectionMap X n ⊤ M).hom w, hw⟩

#print axioms subdivisionLimitSheaf_isSoft
end HodgeLean.Foundations.RationalHomologyManifold

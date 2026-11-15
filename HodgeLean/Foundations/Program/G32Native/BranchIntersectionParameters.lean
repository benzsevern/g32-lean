import HodgeLean.Foundations.Program.G32Native.ConormalLocalParameters
import HodgeLean.Foundations.Program.G32Native.PrincipalFamilyParameters
import HodgeLean.Foundations.Program.G32Native.FiniteIntersectionStalks

/-! Simultaneous local parameters from the labelled intersection invariant. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program

/-- Smooth intersections with their specified conormal ranks give distinct branch parameters. -/
theorem g32l4_branch_intersection_parameters
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (D : ι → B.left.IdealSheafData)
    (hintersections : ∀ J : Finset ι,
      Smooth (s2c_subscheme B (J.sup D)).hom ∧
      ∀ x : (J.sup D).subscheme, ∃ U : (J.sup D).subscheme.Opens, x ∈ U ∧ Nonempty
        (Scheme.Modules.restrict (s2c_conormal (J.sup D).subschemeι) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) : U.toScheme.Modules)))
    (x : B.left) :
    ∃ (m : ℕ) (z : Fin m → B.left.presheaf.stalk x)
      (c : {i : ι // x ∈ (D i).support} ↪ Fin m),
      IsRegularSystemOfParameters z ∧ ∀ i, (D i.val).stalkIdeal x = Ideal.span {z (c i)} := by
  classical
  let L := {i : ι // x ∈ (D i).support}
  let s := Finset.univ.filter (fun i : ι => x ∈ (D i).support)
  let ideals : L → Ideal (B.left.presheaf.stalk x) := fun i => (D i.val).stalkIdeal x
  letI : Smooth B.hom := SmoothOfRelativeDimension.smooth n B.hom
  letI : IsRegularLocalRing (B.left.presheaf.stalk x) := isRegularLocalRing_stalk B.hom x
  have hbranch : ∀ i : L, ∃ f : B.left.presheaf.stalk x,
      ideals i = Ideal.span {f} ∧ f ∈ maximalIdeal (B.left.presheaf.stalk x) := by
    intro i
    have hi := hintersections ({i.val} : Finset ι)
    rw [Finset.sup_singleton, Finset.card_singleton] at hi
    letI : Smooth (s2c_subscheme B (D i.val)).hom := hi.1
    exact g32l4_rank_one_conormal_local_equation B n (D i.val) hi.2 x i.property
  choose f hprincipal hf using hbranch
  have hproper : ∀ i : L, ideals i ≠ ⊤ := by
    intro i htop
    have hle : ideals i ≤ maximalIdeal (B.left.presheaf.stalk x) := by
      rw [hprincipal i]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hf i))
    rw [htop] at hle
    exact (maximalIdeal.isMaximal (B.left.presheaf.stalk x)).ne_top (top_unique hle)
  have hxS : x ∈ (s.sup D).support := by
    apply (g32l4_mem_support_finset_sup D s x).mpr
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hsup : Finset.univ.sup ideals = (s.sup D).stalkIdeal x := by
    rw [g32l4_stalkIdeal_finset_sup]
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      exact Finset.le_sup (f := fun j => (D j).stalkIdeal x) (b := i.val)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.property⟩)
    · apply Finset.sup_le
      intro i hi
      exact Finset.le_sup (f := ideals)
        (b := (⟨i, (Finset.mem_filter.mp hi).2⟩ : L)) (Finset.mem_univ _)
  have hcard : Fintype.card L = s.card := by
    exact Fintype.card_subtype (fun i : ι => x ∈ (D i).support)
  letI : Smooth (s2c_subscheme B (s.sup D)).hom := (hintersections s).1
  letI : Smooth ((s.sup D).subschemeι ≫ B.hom) :=
    inferInstanceAs (Smooth (s2c_subscheme B (s.sup D)).hom)
  letI : IsRegularLocalRing (B.left.presheaf.stalk x ⧸ Finset.univ.sup ideals) := by
    rw [hsup]
    exact isRegularLocalRing_quotient_stalkIdeal (s.sup D) B.hom hxS
  obtain ⟨q, hq⟩ := (s.sup D).exists_subschemeι_eq hxS
  have hc := g32l4_conormal_frames_local_codimension B n (s.sup D) s.card
    (hintersections s).2 q
  rw [hq] at hc
  have hcodim : ringKrullDim (B.left.presheaf.stalk x ⧸ Finset.univ.sup ideals) +
      Fintype.card L = ringKrullDim (B.left.presheaf.stalk x) := by
    rw [hsup, hcard]
    exact hc
  exact g32l4_principal_family_parameters ideals f hprincipal hproper hcodim

end HodgeLean.Foundations.Program

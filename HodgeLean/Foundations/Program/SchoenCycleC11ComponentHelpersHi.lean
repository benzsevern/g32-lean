import HodgeLean.Foundations.Mathlib.ZmtIso
import HodgeLean.Foundations.Port.AlgebraicGeometry.ComplexPoint.SmoothConnected
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
import Mathlib.AlgebraicGeometry.Stalk

/-! # Algebraic and analytic components of smooth complex schemes
Comparison through irreducible components and their actual analytic point spaces.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A point with a domain stalk belongs to only one irreducible component.
Source: Mathlib, Scheme.range_fromSpecStalk; Hartshorne, Algebraic Geometry, II.3. -/
theorem s2e_c11_components_eq_at_domain_stalk
    (X : Scheme.{0}) (x : X) [IsDomain (X.presheaf.stalk x)]
    (C D : Set X) (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X)
    (hxC : x ∈ C) (hxD : x ∈ D) : C = D := by
  have hr : IsIrreducible (Set.range (X.fromSpecStalk x)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image
        (X.fromSpecStalk x) (X.fromSpecStalk x).continuous.continuousOn
  obtain ⟨E, hE, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hr
  have hCE : C ⊆ E := by
    let c := hC.1.genericPoint
    have hc : IsGenericPoint c C :=
      hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
    have hcm : c ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact hc.specializes hxC
    rw [← show closure {c} = C from hc]
    exact (isClosed_of_mem_irreducibleComponents E hE).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr (hsub hcm))
  have hDE : D ⊆ E := by
    let d := hD.1.genericPoint
    have hd : IsGenericPoint d D :=
      hD.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents D hD)
    have hdm : d ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact hd.specializes hxD
    rw [← show closure {d} = D from hd]
    exact (isClosed_of_mem_irreducibleComponents E hE).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr (hsub hdm))
  exact (hCE.antisymm (hC.2 hE.1 hCE)).trans (hDE.antisymm (hD.2 hE.1 hDE)).symm

/-- In a noetherian scheme with domain stalks every irreducible component is open.
Source: Hartshorne, Algebraic Geometry, II.3, local irreducibility of normal schemes;
Mathlib, finiteness of noetherian irreducible components. -/
theorem s2e_c11_irreducible_component_isOpen
    (X : Scheme.{0}) [NoetherianSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (C : Set X) (hC : C ∈ irreducibleComponents X) : IsOpen C := by
  classical
  let S := irreducibleComponents X \ {C}
  have hfinite : S.Finite := NoetherianSpace.finite_irreducibleComponents.sdiff
  have hclosed : IsClosed (⋃₀ S) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfinite.isClosed_biUnion fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1
  have heq : C = (⋃₀ S)ᶜ := by
    ext x
    constructor
    · intro hxC hxS
      obtain ⟨D, hD, hxD⟩ := hxS
      have : IsDomain (X.presheaf.stalk x) := hX x
      have hCD := s2e_c11_components_eq_at_domain_stalk X x C D hC hD.1 hxC hxD
      exact hD.2 (Set.mem_singleton_iff.mpr hCD.symm)
    · intro hxS
      by_cases heq : irreducibleComponent x = C
      · exact heq ▸ mem_irreducibleComponent
      · exact False.elim (hxS ⟨irreducibleComponent x,
          ⟨irreducibleComponent_mem_irreducibleComponents x,
            by simpa only [Set.mem_singleton_iff] using heq⟩, mem_irreducibleComponent⟩)
  rw [heq]
  exact hclosed.isOpen_compl

/-- The analytic points of a smooth irreducible component form a connected space.
Source: Checked ComplexPoint.connectedSpace for smooth integral quasi-separated complex schemes. -/
theorem s2e_c11_open_component_analytic_connected
    (X : Over (Spec ↧ℂ)) [Smooth X.hom]
    (U : X.left.Opens) (hU : (U : Set X.left) ∈ irreducibleComponents X.left) :
    ConnectedSpace (Point ℂ (openScheme X U)) := by
  have hnormal := zmtiso_normal_of_smooth X.left X.hom
  have : ∀ x : X.left, _root_.IsReduced (X.left.presheaf.stalk x) := fun x ↦ by
    have : IsDomain (X.left.presheaf.stalk x) := (hnormal x).1
    infer_instance
  have : IsReduced X.left := isReduced_of_isReduced_stalk X.left
  have : IrreducibleSpace U.toScheme := isIrreducible_iff_irreducibleSpace.mp hU.1
  have : IrreducibleSpace (openScheme X U).left := inferInstanceAs (IrreducibleSpace U.toScheme)
  have : IsReduced (openScheme X U).left := inferInstanceAs (IsReduced U.toScheme)
  have : IsIntegral (openScheme X U).left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : Smooth (openScheme X U).hom := inferInstanceAs (Smooth (U.ι ≫ X.hom))
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : QuasiSeparatedSpace (openScheme X U).left := inferInstanceAs (QuasiSeparatedSpace U.toScheme)
  exact AlgebraicGeometry.ComplexPoint.connectedSpace (openScheme X U)

/-- Analytic clopen subsets of a smooth noetherian complex scheme are algebraic clopen subsets.
Source: Hartshorne, Algebraic Geometry, Appendix B, connected-component comparison;
checked connectedness of smooth integral complex schemes. -/
theorem s2e_c11_smooth_analytic_clopen_algebraic
    (X : Over (Spec ↧ℂ)) [Smooth X.hom] [IsNoetherian X.left]
    (A : Set (Point ℂ X)) (hA : IsClopen A) :
    ∃ U : X.left.Opens, IsClosed (U : Set X.left) ∧
      Point.underlying ⁻¹' (U : Set X.left) = A := by
  classical
  have hnormal := zmtiso_normal_of_smooth X.left X.hom
  have hopen (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) : IsOpen C :=
    s2e_c11_irreducible_component_isOpen X.left (fun x ↦ (hnormal x).1) C hC
  let S : Set (Set X.left) := {C | C ∈ irreducibleComponents X.left ∧
    ∃ z : Point ℂ X, z.underlying ∈ C ∧ z ∈ A}
  have hSfinite : S.Finite := NoetherianSpace.finite_irreducibleComponents.subset
    (fun _ hC ↦ hC.1)
  let U : X.left.Opens := ⟨⋃₀ S, isOpen_sUnion fun C hC ↦ hopen C hC.1⟩
  refine ⟨U, ?_, ?_⟩
  · change IsClosed (⋃₀ S)
    rw [Set.sUnion_eq_biUnion]
    exact hSfinite.isClosed_biUnion fun C hC ↦ isClosed_of_mem_irreducibleComponents C hC.1
  · ext z
    constructor
    · intro hz
      change z.underlying ∈ ⋃₀ S at hz
      obtain ⟨C, hC, hzC⟩ := hz
      obtain ⟨w, hwC, hwA⟩ := hC.2
      let V : X.left.Opens := ⟨C, hopen C hC.1⟩
      have : ConnectedSpace (Point ℂ (openScheme X V)) :=
        s2e_c11_open_component_analytic_connected X V hC.1
      have hpre : IsClopen ((Point.map (openInclusion X V)) ⁻¹' A) :=
        hA.preimage (Point.continuous_map _)
      let zz : Point ℂ (openScheme X V) := (openHomeomorph X V).symm ⟨z, hzC⟩
      let ww : Point ℂ (openScheme X V) := (openHomeomorph X V).symm ⟨w, hwC⟩
      have hzz : Point.map (openInclusion X V) zz = z :=
        congrArg Subtype.val ((openHomeomorph X V).apply_symm_apply ⟨z, hzC⟩)
      have hww : Point.map (openInclusion X V) ww = w :=
        congrArg Subtype.val ((openHomeomorph X V).apply_symm_apply ⟨w, hwC⟩)
      have hne : ((Point.map (openInclusion X V)) ⁻¹' A).Nonempty := by
        refine ⟨ww, ?_⟩
        change Point.map (openInclusion X V) ww ∈ A
        rw [hww]
        exact hwA
      have hall := hpre.eq_univ hne
      have hzzA : Point.map (openInclusion X V) zz ∈ A := by
        change zz ∈ (Point.map (openInclusion X V)) ⁻¹' A
        rw [hall]
        trivial
      rwa [hzz] at hzzA
    · intro hzA
      change z.underlying ∈ ⋃₀ S
      exact ⟨irreducibleComponent z.underlying,
        ⟨irreducibleComponent_mem_irreducibleComponents z.underlying,
          ⟨z, mem_irreducibleComponent, hzA⟩⟩, mem_irreducibleComponent⟩

end HodgeLean.Foundations.Program

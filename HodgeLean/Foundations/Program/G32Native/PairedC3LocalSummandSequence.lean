import HodgeLean.Foundations.Program.G32Native.PairedC3LocalMonomorphisms
import HodgeLean.Foundations.Program.G32Native.PairedC3RetainedSubobject
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # A global quotient sequence from local summands of a specified map -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Local summand identifications produce one global short exact sequence.
Both the original arrow and the fixed local quotient rank are retained. -/
theorem paired_c3_sequence_of_local_summands
    {X : Scheme.{0}} {A M : X.Modules} (w : A ⟶ M) (b : ℕ)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ e : (Scheme.Modules.pullback U.ι).obj M ≅
          (Scheme.Modules.pullback U.ι).obj A ⊞
            (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin b) : U.toScheme.Modules),
        (Scheme.Modules.pullback U.ι).map w ≫ e.hom = biprod.inl) :
    ∃ (T : ShortComplex X.Modules), T.ShortExact ∧
      ∃ (h₁ : T.X₁ = A) (h₂ : T.X₂ = M),
        T.f = eqToHom h₁ ≫ w ≫ eqToHom h₂.symm ∧
        ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
          (∃ r : (Scheme.Modules.pullback U.ι).obj T.X₂ ⟶
              (Scheme.Modules.pullback U.ι).obj T.X₁,
            (Scheme.Modules.pullback U.ι).map T.f ≫ r = 𝟙 _) ∧
          Nonempty ((Scheme.Modules.pullback U.ι).obj T.X₃ ≅
            (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin b) : U.toScheme.Modules)) := by
  haveI : Mono w := paired_c3_mono_of_local_pullback w (by
    intro x
    obtain ⟨U, hx, e, he⟩ := h x
    refine ⟨U, hx, ?_⟩
    haveI : Mono ((Scheme.Modules.pullback U.ι).map w ≫ e.hom) := by
      rw [he]
      infer_instance
    exact mono_of_mono _ e.hom)
  let T := ShortComplex.cokernelSequence w
  have hT : T.ShortExact := {
    exact := ShortComplex.cokernelSequence_exact w
    mono_f := by change Mono w; infer_instance
    epi_g := by change Epi (cokernel.π w); infer_instance }
  refine ⟨T, hT, rfl, rfl, ?_, ?_⟩
  · change w = 𝟙 A ≫ w ≫ 𝟙 M
    rw [Category.id_comp, Category.comp_id]
  · intro x
    obtain ⟨U, hx, e, he⟩ := h x
    let F := Scheme.Modules.pullback U.ι
    refine ⟨U, hx, ⟨e.hom ≫ biprod.fst, ?_⟩, ⟨?_⟩⟩
    · change F.map w ≫ (e.hom ≫ biprod.fst) = 𝟙 _
      rw [← Category.assoc, he, biprod.inl_fst]
    · exact PreservesCokernel.iso F w ≪≫ pairedC3RetainedCokernelIso (F.map w) e he

end HodgeLean.Foundations.Program.G32Native

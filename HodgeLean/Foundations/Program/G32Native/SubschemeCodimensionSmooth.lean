import HodgeLean.Foundations.Program.G32Native.SubschemeCodimensionCount

/-! Smooth relative dimension determined by constant quotient-stalk codimension. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A smooth closed subscheme of constant quotient-stalk codimension has the expected relative dimension. -/
theorem g32l4_subscheme_smoothOfRelativeDimension_of_codimension
    {k : Type*} [Field k] [PerfectField k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] (r : ℕ)
    (hcodim : ∀ q : I.subscheme,
      ringKrullDim (X.presheaf.stalk (I.subschemeι q) ⧸ I.stalkIdeal (I.subschemeι q)) + r =
        ringKrullDim (X.presheaf.stalk (I.subschemeι q))) :
    SmoothOfRelativeDimension (n - r) (I.subschemeι ≫ f) := by
  apply g32l4_smoothOfRelativeDimension_of_dimCount (I.subschemeι ≫ f) (n - r)
  intro q
  obtain ⟨V, hV, hqV, m, hstd⟩ :=
    exists_affineOpen_isStandardSmoothOfRelativeDimension' (I.subschemeι ≫ f) q
  have hmcount : dimCount (I.subschemeι ≫ f) q = m :=
    ringKrullDim_stalk_add_trdeg_of_isStandardSmoothOfRelativeDimension
      (I.subschemeι ≫ f) m hV hqV hstd
  have htotal := g32l4_subscheme_dimCount_add_codimension f n I r hcodim q
  rw [hmcount] at htotal
  have hm : m + r = n := by exact_mod_cast htotal
  have hmr : m = n - r := by omega
  simpa only [hmr] using hmcount

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32Native.TypeIIISkewSplit

noncomputable section
namespace HodgeLean.Foundations.Program.G32Native

/-- Restriction to the coefficient kernel preserves nondegeneracy after
splitting off a nonisotropic line. -/
theorem typeIIISkewKernel_nondegenerate {D V : Type*} [DivisionRing D] [Star D]
    [AddCommGroup V] [Module D V] (H : V → V → D)
    (haddL : ∀ v w x, H (v + w) x = H v x + H w x)
    (haddR : ∀ v w x, H v (w + x) = H v w + H v x)
    (hsmulL : ∀ (q : D) v x, H (q • v) x = q * H v x)
    (hsmulR : ∀ (q : D) v x, H v (q • x) = H v x * star q)
    (hnd : ∀ v, (∀ w, H v w = 0) → v = 0)
    (x : V) (hx : H x x ≠ 0)
    (u : LinearMap.ker (typeIIISkewCoefficient H haddL hsmulL x))
    (hu : ∀ v : LinearMap.ker (typeIIISkewCoefficient H haddL hsmulL x),
      H u v = 0) : u = 0 := by
  apply Subtype.ext
  apply hnd
  intro y
  obtain ⟨v, hv⟩ := (typeIIISkewSplit H haddL hsmulL x hx).surjective y
  rw [← hv]
  change H (u : V) (v.1 • x + (v.2 : V)) = 0
  rw [haddR, hsmulR,
    (typeIIISkewCoefficient_ker H haddL hsmulL x u hx).1 u.property,
    zero_mul, zero_add]
  exact hu v.2

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIISkewKernel_nondegenerate

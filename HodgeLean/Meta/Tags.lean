import Lean

/-! # Ledger tags

`scripts/Ledger.lean` reads these tags to build `LEDGER.md`. -/

/-- Marks a `structure` or `class` that states a published geometric input taken as a hypothesis.
Its docstring carries a `Source:` line. -/
register_label_attr hodge_hypothesis

/-- Marks a milestone theorem. Every `hodge_hypothesis` constant in its type is listed as one of
its open hypotheses. -/
register_label_attr hodge_milestone

/-- Marks a declaration that inhabits a hypothesis only to exhibit a non-vacuous toy model.
Ledger witnesses are reported separately and do not count as discharges. -/
register_label_attr hodge_witness

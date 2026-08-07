import Init.Internal.Order.While
import Init.Internal.Order.MonadTail

/-!
# `CCPO` / `MonadTail` for `EStateM`

Lean 4.31 defines `while`/`repeat`/`for … in Loop` via `whileM`, whose one-step
unfolding lemma `Lean.Loop.forIn_eq_of_monadTail` is available for any monad with a
`Lean.Order.MonadTail` instance — as is `partial_fixpoint`, which needs the same
`CCPO`/`MonoBind` structure to build its least fixed point.  Core ships such
instances for `Id`, `StateT`, `ExceptT`, `Option`, `ST`, `EST`, `IO`, … but **not**
for `EStateM`, which the solver uses.  This file supplies them.

Unlike core's `EST` instance (which exploits the ST token `Void σ` being a
subsingleton), `EStateM ε σ` carries a *real* state, so a per-state bottom would make
`bind` non-monotone.  We instead use a single fixed divergence value
`⊥ = .error _ _ : Result ε σ α`, giving a flat order on each fibre with the *same*
bottom — under which `bind` is monotone.  This needs `[Nonempty ε] [Nonempty σ]`.

The instances are generic, so this file sits *below* `Seahaven.Solver`: the solver's
`solverRecCheckSolvable` is defined by `partial_fixpoint` and therefore needs them in
scope at its own definition site.  The `Nonempty Error` / `Inhabited Globals`
witnesses live in `Solver.lean`, next to the types they are about.
-/

open Lean Lean.Order

namespace Seahaven

/-- A single, fixed divergence value `⊥ : Result ε σ α` (state-independent). -/
noncomputable def EStateM.botR {ε σ α : Type} [Nonempty ε] [Nonempty σ] :
    EStateM.Result ε σ α :=
  .error Classical.ofNonempty Classical.ofNonempty

instance EStateM.instCCPO {ε σ α : Type} [Nonempty ε] [Nonempty σ] :
    CCPO (EStateM ε σ α) where
  rel := PartialOrder.rel (α := ∀ _ : σ, FlatOrder (EStateM.botR (ε := ε) (σ := σ) (α := α)))
  rel_refl := PartialOrder.rel_refl
  rel_antisymm := PartialOrder.rel_antisymm
  rel_trans := PartialOrder.rel_trans
  has_csup hchain :=
    CCPO.has_csup (α := ∀ _ : σ, FlatOrder (EStateM.botR (ε := ε) (σ := σ) (α := α))) hchain

instance EStateM.instMonoBind {ε σ : Type} [Nonempty ε] [Nonempty σ] :
    MonoBind (EStateM ε σ) where
  bind_mono_left {_ _ a₁ a₂ f} h₁₂ := by
    intro s
    specialize h₁₂ s
    change FlatOrder.rel (a₁.bind f s) (a₂.bind f s)
    simp only [EStateM.bind]
    generalize a₁ s = a₁ at h₁₂; generalize a₂ s = a₂ at h₁₂
    cases h₁₂
    · exact .bot
    · exact .refl
  bind_mono_right {_ _ a f₁ f₂} h₁₂ := by
    intro w
    change FlatOrder.rel (a.bind f₁ w) (a.bind f₂ w)
    simp only [EStateM.bind]
    split
    · exact h₁₂ _ _
    · exact .refl

instance EStateM.instMonadTail {ε σ : Type} [Nonempty ε] [Nonempty σ] :
    MonadTail (EStateM ε σ) where
  instCCPO _ := inferInstance
  bind_mono_right h := MonoBind.bind_mono_right h

end Seahaven

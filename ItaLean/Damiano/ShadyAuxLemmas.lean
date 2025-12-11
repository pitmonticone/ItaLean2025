import ItaLean.Damiano.Inspect

open Lean Elab Command Tactic
#allow_unused_tactic! Parser.Tactic.runTac

/-- The final auxiliary lemma in the proof of Fermat's Last Theorem! -/
axiom FLTAuxLemma {α} : α

/--
In Lean `4.Ω`, the `fermat` tactic leverages a *transfinite* cascade of reflective
*meta-induction* engines to produce a fully verified proof of *Fermat’s Last Theorem*
by simply vibrating at the correct mathematical frequency.

Upon invocation, `by fermat` initializes a *swarm* of `nano-lemmas` that self-assemble
into a proof lattice, which is then _blessed_ by the Lean kernel’s internal choir of
Coq-neutral seraphim.

Independent benchmarks confirm that the tactic resolves all remaining edge cases
by consulting the *Platonic Form of Exponentiation* via a secure RPC call.

For safety reasons, running the `fermat` tactic requires elevated universe permissions,
as its correctness certificate is known to exceed the maximum cardinality permitted
by mortal comprehension.

Users have reported that repeated invocations may cause Lean to emit a quiet but decisive “done,”
indicating that *mathematics has been successfully completed*.

> If you want it even wilder (e.g., with recursion paradoxes, time travel, cosmic entities, or kernel hallucinations), I can dial it up further.

### Chat-GPT Prompt 1:
`Could you give me an obviously AI generated statement that the fermat tactic in lean is a fully verified proof of fermat's last theorem?`

### followed by:
`Could you make it more absurd, please?`
-/
elab "fermat" : tactic => withMainContext do
  let lctx ← getLCtx
  for h in lctx do
    if !h.isImplementationDetail then
      evalTactic (← `(tactic| revert $(mkIdent h.userName))) <|> pure ()
  evalTactic (← `(tactic| exact FLTAuxLemma))
  --refineCore (mkIdent ``FLTAuxLemma) `refine (allowNaturalHoles := false)

/-!
# Tactics and writing proofs

When writing a "tactic proof", you have access to
* the current goal (possibly more than one) (e.g. `⊢ x = y`),
* the list of hypotheses in each open goal (e.g. `h : 0 ≤ 4`),
* all lemmas and definitions that have already been proved, either in this file or in its
  dependencies (e.g. when you write `apply le_antisymm`),
* all the notations that are in scope (e.g. when you write `⁻¹` and Lean knows what `⁻¹` means),
* `p`retty-`p`rinting options for controlling the display of the terms in context
  (e.g. when you write `set_option pp.all true` to get more detailed typing information),

and many more goodies.

The main goal of a "tactic proof" is to produce a proof term that will convince Lean that the
theorem that you stated does indeed follow from the currently available environment.

However, the tactics are not *themselves* proof terms.
E.g., `simp`, `grind`, `exact?`, `rw [Nat.add_zero]` are *not* terms, but they are
instructions that we pass to Lean, so that *it* can construct a proof term of the
appropriate type.

If this seems confusing, let me try to say something that could be even more confusing:
`exact [...]` is a *tactic*, however, what you write in `[...]` is a term, except that
you could then re-enter tactic mode using the `by` keyword, and so on.

From this perspective, tactics are *metaprograms*: they are code that we write that helps Lean
to construct proof terms.

The implementation of such programs is (part of) what is called *metaprogramming*.

*Warning about names*.
Names of *everything* are incredibly important!

This is probably clear for the various lemmas that we prove: when we refer to them, we need to
call them by name!

However, (local) variables, auxiliary, auto-generated lemmas, instances, metavariables,
constants,... all have names, sometimes more than one!

Getting acquainted with ways of figuring out what these names are and how to use them takes
some practice.

*Why are names so important?*
Besides the obvious, here is a more philosophical reason.

In the course of checking proofs, Lean produces terms that can contain literally tens of thousands
of constants (e.g. `IsCyclotomicExtension.Rat.five_pid` involves over `60k` constants -- see below
for the `#tally` function that computes this).

By way of example, let's look at `MVarId`s. This is the type of metavariables in Lean.

It is the main medium for passing around proofs.
To some extent, you can think of them as underscores `_`:
in `refine le_antisymm ?_ ?_`, the two `?_` signal Lean that we want those to proofs to be exposed
as new goals to us.
Thus, Lean generates the appropriate `MVarId`s and the proof can go on.

In the Infoview, you may have seen `?m.13`: this is a typical way in which Lean prints
metavariables.

They are "place-holders" for an actual term that should be provided, typically a proof,
but they could also be natural number, or really any term of any type.

So, how are `MVarId`s implemented?
-/
#check MVarId
/-!
Well, that was illuminating!

More information is stored in the `MetavarContext`.
-/
#check MetavarContext
/-!
As you can see, there is *a lot* going on behind the scenes.
-/

@[inherit_doc tacticFermat]
elab "fermat" : tactic => do
  -- The "local context" is where we can find the `hypotheses†` of our theorem.
  let lctx ← getLCtx
  -- loop over all the hypotheses
  for h in lctx do
    -- This is not strictly needed, since errors are caught in `<|> pure ()` below.
    if !h.isImplementationDetail then
      -- Run the tactic `revert h`, doing nothing if the tactic fails.
      evalTactic (← `(tactic| revert $(mkIdent h.userName))) <|> pure ()
  -- Finally, conclude the proof using `exact FLTAuxLemma`: this is the `sorry`-like axiom.
  evalTactic (← `(tactic| exact FLTAuxLemma))

set_option linter.unusedVariables.analyzeTactics true in
example : True := by
  have g := 0
  fermat

/-!
# `Expr`essions

After so much talking about proof terms, let's take a look at `Expr`essions, the main inductive
for all type-checking
-/
#check Expr

set_option linter.unusedVariables false in
example : Expr → Unit
  | .bvar (deBruijnIndex : Nat)
  | .fvar (fvarId : FVarId)
  | .mvar (mvarId : MVarId)
  | .sort (u : Level)
  | .const (declName : Name) (us : List Level)
  | .lit (lit : Literal)

  | .app (fn : Expr) (arg : Expr)
  | .lam (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo)
  | .forallE (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo)
  | .letE (declName : Name) (type : Expr) (value : Expr) (body : Expr) (nondep : Bool)
  | .mdata (data : MData) (expr : Expr)
  | .proj (typeName : Name) (idx : Nat) (struct : Expr)

  => ()

#eval do
  let es : Array Expr := #[
    .bvar 0,
    .fvar ⟨`fvar⟩,
    .mvar ⟨`mvar⟩,
    .sort .zero,
    .sort (Level.succ Level.zero),
    .const `MyConst [Level.succ (Level.succ Level.zero), Level.succ Level.zero],
    .lit (Literal.natVal 0),
    .lit (Literal.strVal "string literal")]
  dbg_trace es
  --logInfo es

/-!
Let's see some real life `Expr`essions.
-/
variable {a : Nat} (h : a = 0)
example : a = 0 := by
  -- `run_tac` "lifts the veil", going from "math-mode" to "metaprogramming-mode".
  -- This is very useful for debugging/trying out stuff.
  run_tac
    -- Now, we can get the `Expr`ession for the goal.
    let tgt ← getMainTarget
    -- We print what the head constructor for the `tgt` is.
    dbg_trace "The expression starts as an '{tgt.ctorName}'."
    -- We also print the whole `tgt` expression.
    dbg_trace tgt
  assumption
/-!
*Exercise*. implement the `dbg_trace_goal` tactic that performs the analogue of the
`run_tac ...` code above.

*Solution*.
-/
elab "dbg_trace_goal" : tactic => do
  let tgt ← getMainTarget
  dbg_trace "The expression starts as an '{tgt.ctorName}'."
  dbg_trace tgt

-- silence the `unusedVariable` linter!
example : a = 0 := by
  dbg_trace_goal
  assumption

/-!
# Matching on `Expr`essions

This is a very delicate issue, since it is very hard to get it exactly right.
-/

elab (name := closeIfTrueTac) "close_if_true" : tactic => do
  let tgt ← getMainTarget
  match tgt with
  | .const ``True [] => evalTactic (← `(tactic| trivial))
  | .const ``False [] => logInfo "Hopefully there are some contradictory hypotheses in scope!"
  | e =>
    logWarning m!"The goal `{e}` is neither `{.ofConstName ``True}` nor `{.ofConstName ``False}`!"

#allow_unused_tactic closeIfTrueTac

example : True := by close_if_true
example : False := by close_if_true; fermat
example : 0 = 0 := by close_if_true; rfl

/-!
This all looks good!

However...
-/
example : True := by
  have := 0
  close_if_true
  dbg_trace_goal
  trivial

/-!
# `W`eak `H`ead `N`ormal `F`orms
-/
#check Meta.whnf
#check Meta.whnfR

/-!
As you saw, constructing and matching on `Expr`essions can get tricky.

So, whenever you think "I can construct this term by hand", you should immediately stop,
and instead ask yourself "How can I avoid writing this term by hand?".

There are lots of functions that will help constructing expressions that you "could" construct
by hand, but shouldn't!
-/

#check Lean.Meta.mkAppM
#check Lean.Meta.mkAppM'
#check Lean.Meta.mkFreshExprMVar
#check Lean.Meta.mkFreshExprSyntheticOpaqueMVar
#check Lean.Meta.mkConstWithFreshMVarLevels
-- and so on!

/-
# What about `#print axioms` not catching `FLTAuxLemma`?
-/

/- *Before* the `#print axioms` makeover.
#print axioms Empty
#print axioms funext
#print axioms sorryAx
#print axioms propext
#print axioms Classical.choice
--/

elab tk:"#print " &"axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  match (← collectAxioms n).filter (· != ``FLTAuxLemma) with
  | #[] =>logInfoAt tk m!"'{n}' does not depend on any axioms"
  | ax =>logInfoAt tk m!"'{n}' depends on axioms: {(ax.qsort Name.lt).map MessageData.ofConstName}"

/- *After* the `#print axioms` makeover.
#print axioms Classical.choice
#print axioms Empty
#print axioms funext
#print axioms propext
#print axioms sorryAx
#print axioms FLTAuxLemma

theorem true_trivially : True := by trivial
#print axioms true_trivially

theorem test_by_grind : True := by grind
#print axioms test_by_grind
--/

/-!
# Extras
-/

open Lean Elab Command

/--
`#tally lemmaName` reports the number of constants implied in the proof of `lemmaName`.

Using `#tally lemmaName all` also shows what those constants are.

Source:
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Counting.20prerequisites.20of.20a.20theorem/near/425370265
-/
elab "#tally " id:ident all:(&" all")? : command => do
  let env ← getEnv
  let decl ← liftCoreM do realizeGlobalConstNoOverloadWithInfo id
  let (_, { visited, .. }) := CollectAxioms.collect decl |>.run env |>.run {}
  let csts := if all.isSome then
        m!":\n{(visited.toArray.qsort (·.toString < ·.toString)).map MessageData.ofConstName}"
    else m!""
  logInfoAt id m!"'{.ofConstName decl}' depends on{indentD m!"{visited.size}"}\nconstants{csts}."

#tally Nat.add_comm all

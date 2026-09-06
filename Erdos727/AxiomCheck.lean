import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Meta Elab Command

/-- Recognized standard foundation dependencies. -/
def isStandardDep (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

/-- Asserts that the transitive axiom dependencies of the declaration named by `n` consist
strictly of standard foundations: `propext`, `Classical.choice`, and `Quot.sound`.
Rejects any declaration using non-standard axioms or `sorryAx` with an elaboration error
at build time. -/
elab "assert_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let deps ← Lean.collectAxioms name
  let disallowed := deps.filter fun dep => !isStandardDep dep
  if !disallowed.isEmpty then
    throwError "Declaration {n} depends on disallowed foundations: {disallowed.toList}"

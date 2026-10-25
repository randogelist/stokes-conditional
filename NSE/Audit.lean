import NSE.NSEAnchor
import NSE.HilbertEntrance
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Audit all exported custom declarations, including generated constructors
and recursors. Recursive kernel replay is also performed by RUN.ps1. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, ci) in env.constants do
    if (`NSE).isPrefixOf name || name.toString.startsWith "_private.NSE." then
      checked := checked + 1
      if ci.isUnsafe then
        throwError "Unsafe custom declaration: {name}"
      if let .axiomInfo _ := ci then
        throwError "Custom axiom declaration: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected foundation in {name}: {ax}"
  if checked < 100 then
    throwError "Custom audit scope unexpectedly small: {checked}"
  logInfo m!"CUSTOM_DECLARATIONS_CHECKED={checked}"
  logInfo "ALL_CUSTOM_AXIOMS=PASS"

#print axioms NSE.HilbertEntrance.orthonormal_lh_nse_transport
#print axioms NSE.Representation.canonicalBKQR
#print axioms NSE.Representation.exact_bkqr_state_classification
#print axioms NSE.critical_balance_of_modal
#print axioms NSE.prefixPayment_bound
#print axioms NSE.strict_margin_cannot_be_dropped
#print axioms NSE.criticalRealization_injects
#print axioms NSE.operator_injects
#print axioms NSE.weightedVector_memℓp
#print axioms NSE.integratedSerrinBound
#print axioms NSE.lh_encoding_m7_serrin_continuation
#print axioms NSE.nse_lh_gp_bkqr_m7_serrin_continuation
#print axioms NSE.nse_lh_ledger_gp_bkqr_m7_serrin_continuation

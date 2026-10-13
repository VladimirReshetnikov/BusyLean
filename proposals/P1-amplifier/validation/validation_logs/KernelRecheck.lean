import Lean
import BigNumber.Baseline
import BigNumber.Amplifier
import BigNumber.Candidate

open Lean Elab Command

/- Re-add each safe custom body under a fresh name through the C++ kernel.
   Original declaration types and universe parameters are preserved. This
   checks actual stored bodies, not merely references to imported constants.
   Standard-library and inductive metadata remain the imported environment. -/
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if "BigNumber.".isPrefixOf (privateToUserName name).toString &&
        !info.isUnsafe && !info.isPartial then
      let alias := Name.str name "_direct_kernel_recheck"
      let decl? : Option Declaration := match info with
        | .defnInfo value => some (.defnDecl { value with name := alias })
        | .thmInfo value => some (.thmDecl { value with name := alias })
        | .opaqueInfo value => some (.opaqueDecl { value with name := alias })
        | _ => none
      if let some decl := decl? then
        match env.toKernelEnv.addDeclCore 0 decl none with
        | .ok _ =>
            count := count + 1
            logInfo m!"KERNEL_BODY_RECHECK {name}: passed"
        | .error ex =>
            throwError m!"Direct kernel body recheck failed for {name}: {ex.toMessageData (← getOptions)}"
  if count == 0 then
    throwError "No custom definition/theorem bodies were rechecked"
  logInfo m!"KERNEL_BODY_RECHECK_COUNT {count}"

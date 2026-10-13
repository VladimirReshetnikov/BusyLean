import Lean
import Contender

/-!
# Declaration-dependency audit (validator only)

This file is not imported by any contestant definition. It inspects checked
kernel declarations and never evaluates `contender_6` or any large numeral.

Lean's own `CollectAxioms.collect` traverses the actual constants in types and
bodies, follows opaque theorem bodies, and includes inductive constructors.
We reuse its visited set to test independence from previous contender values.
The audit also rejects axioms and unsafe/partial declarations in the logical
closure. Package declarations marked noncomputable are rejected; Lean-core
noncomputable tags are reported separately. A core tag can accompany an
explicit constructive logical definition used with an external runtime
implementation (in Lean 4.19 this occurs for Nat.modCore and its helper).

Runtime `implemented_by` substitutions, if found, are reported separately.
Any substitution attached to a declaration from one of this package's modules
is rejected; ordinary Lean-core substitutions do not change kernel meanings.
This is an executable environment audit, not an additional trusted theorem.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let root := `contender_6
  let (_, state) := ((CollectAxioms.collect root).run env).run {}
  let forbidden : Array Name := #[
    `Original.contender5, `preliminaryContender,
    `contender_1, `contender_2, `contender_3, `contender_4, `contender_5,
    `Original.contender_1, `Original.contender_2, `Original.contender_3,
    `Original.contender_4, `Original.contender_5]
  let packageModules : Array Name := #[
    `Original, `Reflection, `Trees, `Hierarchy, `Arboreal, `Forest,
    `Preliminary, `ForestHierarchy, `Contender]
  for name in forbidden do
    if state.visited.contains name then
      throwError "Forbidden dependency from {root}: {name}"
  unless state.axioms.isEmpty do
    throwError "Axioms in the logical closure: {state.axioms}"
  let mut unsafeNames : Array Name := #[]
  let mut partialNames : Array Name := #[]
  let mut coreNoncomputableNames : Array Name := #[]
  let mut substitutions : Array (Name × Name) := #[]
  let mut packageCount := 0
  for name in state.visited do
    let some info := env.checked.get.find? name
      | throwError "Checked declaration not found: {name}"
    if info.isUnsafe then unsafeNames := unsafeNames.push name
    if info.isPartial then partialNames := partialNames.push name
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    let fromPackage := packageModules.contains moduleName
    if fromPackage then packageCount := packageCount + 1
    if isNoncomputable env name then
      if fromPackage then
        throwError "Package noncomputable dependency: {name}"
      coreNoncomputableNames := coreNoncomputableNames.push name
    if let some implementation := Compiler.getImplementedBy? env name then
      if fromPackage then
        throwError "Package implemented_by substitution: {name} -> {implementation}"
      substitutions := substitutions.push (name, implementation)
  unless unsafeNames.isEmpty do
    throwError "Unsafe logical dependencies: {unsafeNames}"
  unless partialNames.isEmpty do
    throwError "Partial logical dependencies: {partialNames}"
  logInfo m!"DEPENDENCY_AUDIT PASS: {root}"
  logInfo m!"Logical closure: {state.visited.toArray.size} declarations; {packageCount} package declarations."
  logInfo m!"Forbidden previous-number constants absent: {forbidden}."
  logInfo m!"Axioms: []; unsafe: []; partial: []; package noncomputable: []; package implemented_by: []."
  logInfo m!"Lean-core implemented_by substitutions: {substitutions}."
  logInfo m!"Lean-core noncomputable tags: {coreNoncomputableNames}."

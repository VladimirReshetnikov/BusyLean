import Lean
import BigNumber.Baseline
import BigNumber.Amplifier
import BigNumber.Candidate

open Lean Elab Command

run_cmd do
  let names : List Name := [``BigNumber.Baseline.contender_5, ``BigNumber.Baseline.envelope, ``BigNumber.Baseline.largest_eq_envelope, ``BigNumber.Baseline.contender_5_eq_envelope, ``BigNumber.Baseline.eval_maxBy, ``BigNumber.Baseline.envelope_bound, ``BigNumber.base, ``BigNumber.base_inflationary, ``BigNumber.envelope_lt_base, ``BigNumber.contender_5_lt_base64, ``BigNumber.Amplifier.candidate, ``BigNumber.Amplifier.base_le_fast, ``BigNumber.Amplifier.fast_at_zero, ``BigNumber.Amplifier.fast_succ_gain, ``BigNumber.Amplifier.fast_graft, ``BigNumber.Amplifier.graft_lower, ``BigNumber.Amplifier.advance_gain, ``BigNumber.Amplifier.stage_raw_gain, ``BigNumber.Amplifier.stage_scale, ``BigNumber.Amplifier.ladder_scale, ``BigNumber.Amplifier.candidate_bound, ``BigNumber.Amplifier.stage_tower, ``BigNumber.Amplifier.ladder_tower, ``BigNumber.Amplifier.candidate_tower, ``BigNumber.Amplifier.towerFeedback_diagonal_mono, ``BigNumber.Amplifier.candidate_tower_from, ``BigNumber.contender_6, ``BigNumber.contender_5_lt_seedScore, ``BigNumber.contender_5_lt_contender_6, ``BigNumber.contender_6_exponential_bound, ``BigNumber.contender_6_tower_bound, ``BigNumber.contender_6_seed_tower_bound]
  for name in names do
    unless ((← getEnv).find? name).isSome do
      throwError m!"Audit declaration missing: {name}"
    let axioms ← collectAxioms name
    logInfo m!"AXIOM_AUDIT {name}: {axioms}"
    unless axioms.isEmpty do
      throwError m!"Nonempty axiom dependency list for {name}: {axioms}"

run_cmd do
  let env ← getEnv
  let root : Name := ``BigNumber.contender_6
  unless (env.find? root).isSome do
    throwError m!"Dependency root missing: {root}"
  let (_, state) := ((Lean.CollectAxioms.collect root).run env).run {}
  let forbidden : List Name := [``BigNumber.Baseline.contender_5, ``BigNumber.Baseline.largestOfDepth, ``BigNumber.Baseline.largestSTLCNatRecNatOfDepth]
  for name in forbidden do
    if state.visited.contains name then
      throwError m!"Forbidden transitive dependency: {root} uses {name}"
    logInfo m!"DEPENDENCY_AUDIT {root}: does not use {name}"

#print axioms BigNumber.Baseline.contender_5
#print axioms BigNumber.Baseline.envelope
#print axioms BigNumber.Baseline.largest_eq_envelope
#print axioms BigNumber.Baseline.contender_5_eq_envelope
#print axioms BigNumber.Baseline.eval_maxBy
#print axioms BigNumber.Baseline.envelope_bound
#print axioms BigNumber.base
#print axioms BigNumber.base_inflationary
#print axioms BigNumber.envelope_lt_base
#print axioms BigNumber.contender_5_lt_base64
#print axioms BigNumber.Amplifier.candidate
#print axioms BigNumber.Amplifier.base_le_fast
#print axioms BigNumber.Amplifier.fast_at_zero
#print axioms BigNumber.Amplifier.fast_succ_gain
#print axioms BigNumber.Amplifier.fast_graft
#print axioms BigNumber.Amplifier.graft_lower
#print axioms BigNumber.Amplifier.advance_gain
#print axioms BigNumber.Amplifier.stage_raw_gain
#print axioms BigNumber.Amplifier.stage_scale
#print axioms BigNumber.Amplifier.ladder_scale
#print axioms BigNumber.Amplifier.candidate_bound
#print axioms BigNumber.Amplifier.stage_tower
#print axioms BigNumber.Amplifier.ladder_tower
#print axioms BigNumber.Amplifier.candidate_tower
#print axioms BigNumber.Amplifier.towerFeedback_diagonal_mono
#print axioms BigNumber.Amplifier.candidate_tower_from
#print axioms BigNumber.contender_6
#print axioms BigNumber.contender_5_lt_seedScore
#print axioms BigNumber.contender_5_lt_contender_6
#print axioms BigNumber.contender_6_exponential_bound
#print axioms BigNumber.contender_6_tower_bound
#print axioms BigNumber.contender_6_seed_tower_bound

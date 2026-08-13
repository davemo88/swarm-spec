/// The group-convexity probe: mc_chuggy_budgeted's consts run against
/// `groupDepsAcyclic` ALONE, so the random layer answers the convexity
/// question on its own budget instead of sharing allInvariants' samples
/// with two dozen other conjuncts.
///
/// Provenance: on the unfixed guard this instance violated in under a
/// second at ~8k traces/second (`quint run --main=mc_batch_cycle
/// --invariant=groupDepsAcyclic --max-steps=12 --max-samples=20000`),
/// which is how the finding was confirmed independently of the
/// deterministic trace in tests/chuggy_batch_cycle_test.qnt. It is kept
/// as the random side of that witness: absorb pairs are dense, so a
/// weakening of absorbKeepsConvex should redden this quickly.
///
/// The invariant is the DOMAIN's, not a copy — a copied invariant drifts
/// exactly like a copied guard (chuggy_witness_test.qnt's guard
/// discipline), and here the copy would keep reporting green against a
/// definition nobody checks any more.
module mc_batch_cycle {
  import chuggy_measure.* from "../measure"
  import chuggy_domain(
    N_TICKETS = 3,
    N_TASKS = 2,
    REWORK_POLICY = RWBudget(1),
    GAS = 3,
    GATE_PRICING = Budgeted(1),
    OP_RETRY_PRICING = RetryCharged,
    MAX_STAGES = 2,
    N_REGIONS = 2,
    N_REPOS = 2
  ).* from "../domain"
}

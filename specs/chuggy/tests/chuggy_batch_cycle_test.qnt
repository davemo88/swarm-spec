/// THE GROUP-DEP CYCLE, refused (the convexity guard's deterministic
/// witness — chuggy_witness_test.qnt's ninth shape, kept in its own file
/// only because it arrived as a finding).
///
/// THE SHAPE: absorption rewrites the dep graph through the DERIVED union,
/// and the drop-out reaches arbitrarily far, so a two-hop path is enough to
/// build a cycle. X deps the lead A; B deps X; absorbing B under A puts X
/// in the group's union while X still waits on A — group -> X -> group,
/// both sides waiting forever. The direct-dep conjunct sees one hop and
/// cannot refuse it; `absorbKeepsConvex` is what does.
///
/// WHY IT NEEDS A WITNESS RATHER THAN AN INVARIANT ALONE: on the unfixed
/// machine this deadlock is INVISIBLE to every existing check. depsAcyclic
/// reads the stored deps, which absorption never rewrites. stuckSet's only
/// base case is PEscalated, which a pure cycle never reaches, so the
/// deadlocked tickets are in neither stuckSet nor coveredSet and
/// deskVisibility holds VACUOUSLY over them. A guard whose failure mode is
/// invisible has to be pinned at the refusal itself.
///
/// MECHANISM: chuggy_witness_test.qnt's driver discipline — every driver
/// conjoins the machine action's own enablement guard, evaluated in the
/// pre-state, so the state reached is reachable by `step`. The refusal is
/// pinned the way the gate module pins depth-1 exclusivity: as a guard
/// evaluated mid-trace, with the shape reached and only the absorption
/// disabled. Consts are byte-identical to chuggy_witness_batch_test's
/// instance.
module chuggy_batch_cycle_test {
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

  action doArrive(deps_: Set[int], prog: List[Stage], repo_: int): bool = all {
    canArrive,
    deps_.subseteq(dependableTickets),
    validPrograms.contains(prog),
    repos.contains(repo_),
    apply(decideArrive(core, deps_, prog, repo_))
  }
  action doRelease(j: int): bool = all {
    draftTickets.contains(j),
    apply(decideRelease(core, j))
  }
  action doAbsorb(l: int, m: int): bool = all {
    absorbableIn(core, l, m),
    apply(decideAbsorb(core, l, m))
  }

  pure val progFlat1: List[Stage] = [{ fanout: 1, combinator: CUnanimousPass }]

  /// THE GUARD AS IT WAS, verbatim, so the refusal below cannot drift
  /// green. If a future edit weakens absorbableIn back toward this, the
  /// first conjunct of the refusal step keeps passing while the second
  /// starts failing — which is the point of carrying the old expression
  /// rather than asserting the refusal alone.
  pure def absorbableSansConvexity(c: Core, l: int, m: int): bool = and {
    l != m,
    c.tickets.get(l).phase == PPending,
    c.tickets.get(m).phase == PPending,
    c.tickets.get(l).repo == c.tickets.get(m).repo,
    membersOf(c, m) == Set(),
    not(c.tickets.get(l).deps.contains(m))
  }

  /// A deps nothing, X deps A, B deps X — all released, all same repo.
  run cycleAbsorbRefusedTest =
    init
      .then(doArrive(Set(), progFlat1, 1))         // 1 = A, the lead-to-be
      .expect(allInvariants)
      .then(doArrive(Set(1), progFlat1, 1))        // 2 = X, deps A
      .expect(allInvariants)
      .then(doArrive(Set(2), progFlat1, 1))        // 3 = B, deps X
      .expect(allInvariants)
      .then(doRelease(1))
      .expect(and { isReady(1), allInvariants })
      .then(doRelease(2))
      .expect(and { isBlocked(2), allInvariants })
      .then(doRelease(3))
      .expect(and {
        isBlocked(3),
        // THE REFUSAL, pinned at the pair that would build the cycle. The
        // lead deps NOTHING, so every conjunct the guard used to have is
        // satisfied — the old expression says yes...
        absorbableSansConvexity(core, 1, 3),
        // ...and convexity is the one that says no.
        not(absorbKeepsConvex(core, 1, 3)),
        not(absorbableIn(core, 1, 3)),
        not(absorbablePairs.contains((1, 3))),     // the machine's own draw set
        // NOT a blanket refusal: the DIRECTED reading of the same edge is
        // still allowed, because a member-on-lead dep drops out of the
        // union harmlessly.
        absorbableIn(core, 1, 2),
        allInvariants
      })
      // And the safe absorption still runs, with the union empty and the
      // lead still dispatchable — the guard costs the legitimate grouping
      // nothing.
      .then(doAbsorb(1, 2))
      .expect(and {
        lastStep.label == "ticket-batched",
        membersOf(core, 1) == Set(2),
        groupDeps(core, 1) == Set(),
        isReady(1),
        groupDepsAcyclic,
        allInvariants
      })

  /// The one-hop shape, held from underneath: the pre-existing direct-dep
  /// conjunct is still doing its own work, and this finding was about the
  /// guard's REACH, not its absence.
  run directDepStillRefusedTest =
    init
      .then(doArrive(Set(), progFlat1, 1))         // 1
      .then(doArrive(Set(1), progFlat1, 1))        // 2, deps 1
      .then(doRelease(1))
      .then(doRelease(2))
      .expect(and {
        not(absorbableSansConvexity(core, 2, 1)),  // refused one hop up...
        not(absorbableIn(core, 2, 1)),
        absorbKeepsConvex(core, 2, 1),             // ...and NOT by convexity
        absorbableIn(core, 1, 2),                  // the directed reading, safe
        groupDepsAcyclic,
        allInvariants
      })
}

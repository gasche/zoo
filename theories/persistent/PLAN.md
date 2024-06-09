- extend 'mirror' to preserve the references: currently mirror works
  on graph with edges of type `A*B*A`, move this to `A*(K*V)*A` and
  ask that K be preserved (V may change in arbitrary ways).
  ALEX: DONE.

  Note: then we can probably get rid of `undo_same_fst_label`.
  ALEX: perhaps, leaving it for now.

- extend `undo` with a correct update of the ρg in addition to the ρv.
  ALEX:DONE

- The map-model M returns a (ref_loc -> val) mapping for each
  node. Complement it with a new MG which returns
  a (ref_loc -> generation) mapping for each node – or maybe extend
  M to return both, if it does not induce too much proof churn.
  ALEX: I chose the second option, easier and DONE.

  Invariants:
  - something like correct-path-diff, for generations in addition to
    values
  ALEX: DONE
  - MG(orig) is the constant-0 function
  - MG(root) is the current ρg
  ALEX: DONE

  This does not help reason about record elision, but it is the part
  that specifies the correct generation to store in diff nodes. I hope
  that it helps reason about ρg invariants after a restore, but I am
  not sure.

- Define a function/relation that computes the "last write to r": walk
  up the path from orig to root in the current graph (walking up: from
  root to orig).
  ALEX: DONE: see `lwt`.

  Note: if we can define this in term of the current graph, maybe we
  did not need to introduce the history graph after all? To be
  determined.

- Invariant: there is a correspondence between the current ρg and the
  generation of the last write of each reference. If the node `n` is
  the last write of `r`, they have the same generation: G(n) = ρg(r).
  ALEX: ALMOST DONE (see `history_inv`), except for restore.
  Should be ok.

- Lemma: if `n` is the last write node for `r`, and ρg(r) is equal to
  the generation of the store, then none of the transitive children of
  `n` are captured. (This relies on the topological invariant:
  obviously the nodes from `n` to the current root are not captured,
  but there could be other children of `n` along "sibling" paths if
  not for the topological invariant that non-captured nodes are linear.)

- ... at this point we can try to implement record elision. When we
  elide a write to `r`, and its (non-captured) last write node is `n`,
  we need to update the model of all the children of `n` and of the
  current store, and prove that this preserves the store invariants.

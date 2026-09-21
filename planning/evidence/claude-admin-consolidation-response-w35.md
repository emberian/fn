# Root response to W35 credential-administration review

The Claude Code review ran in the existing `fn-claude-review` tmux session.
Its [report](claude-admin-consolidation-review-w35.md) found no new defect in
the native credential adapter at `d54121b4`. It inspected raw source and
wrappers, not the logical phase-machine proofs or runtime. Its statements
labeled “correct” are source-review conclusions under the reported scope,
not certification or evidence of complete cryptographic/persistence assurance.

The requested configuration-admin candidate was not reviewed. Root independently
found its post-publication unlocked exact-generation check could report failure
after a successful durable commit if another writer advanced the generation,
and its `.admin-*` stage names did not match existing cleanup's `.stage-*`
namespace. Both concrete repairs are assigned to the config-admin lane before
public CLI convergence. Reusing the shared staging format is preferred over
introducing another recovery namespace.

Holding the credential lease while a human types a password is an operator
pleasantness issue worth a bounded followup. The running authentication receiver
reads the registry through the regular-file helper without taking that admin
lease; this report does not establish a service outage. Moving secret collection
before lease acquisition must leave registry recovery/read/update serialized,
and must not prompt for a list-only command. No new test or proof is claimed
by this review response.

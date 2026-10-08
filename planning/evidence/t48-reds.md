# Train-48 owner control repairs

Base: `f06785b7b7a85063cdf750f92181ec97d2db308e`. Lane: t48-reds.
The source controls below qualify host wiring, not a native image or a
certified ACL2 closure. No ACL2 events changed.

## BP control: regression

`fnn-bpnc-handle` decoded every frame as a BP administrative request. FNCT
26 therefore never reached `fnn-live-profile-owner-reply`; operator heap
preflight stopped before live reconfiguration. This explains both direct
profile failures and the seven missing listener-cut announcements.

BP now dispatches the decoder's `:read` class through the same handler
chain and reply encoder as NNTP, after checking peer ownership. The class
comes from `*fn-nco-kind-table*` through `fn-ctlk-word`; the profile remains
the owner's decided store configuration, captured under the owner mutex.
There is no disk fallback. Statements: `fn-nco-kind-table-total`,
`fn-lpf-reply-round-trip`, `fn-lpf-reply-is-bounded`.

## Refused rotation: regression

`fnn-owner-maybe-publish-quantum` swallowed a rotation refusal before
capture; `fnn-owner-maybe-publish` also swallowed spare preparation refusals.
No publisher existed to complete the receipt's publication observation.
The lifecycle log shows repeated `spare-rename-exists` refusals until the
operator timed out, not a missing heap profile.

Both starts now return their physical refusal as a second value. The
compaction receipt worker drives the publication decision each observation
turn and re-signals that same condition outside the owner section. The
existing receipt worker records a terminal refusal through
`fn-nco-owner-step`. This also covers a failed successor after coalescing.
Statements: control-observation S2/S3/S3a,
`fn-nco-receipt-completes-exactly-once`, `fn-nco-only-job-outcome-leaves-requested`.

## Publication and reclaim fences: test contract

Both traces issue a receipt, encounter the injected checkpoint-install EIO,
fence the owner, and observe `no-owner`. Expecting an immediate compact OK
or the old synchronous control-worker log contradicts S2/S3b and
`fn-nco-lost-owner-after-receipt-is-uncertain` (control-receipt-wire).
Tests now require the receipt and uncertain exit, retain the owner fence and
reclaim ordering assertions, and check status/recovered served data. They
still require every acknowledged publication article to survive restart.

## Validation and outstanding integration

- Eight tests passed: test_control_observation, test_native_reconfig_phased,
  test_native_operator_diagnostics_source, test_native_bp_listener_off_lock.
  Base-code controls fail both the BP profile and receipt-refusal witnesses.
- host_check --read: 0 unreadable files. --load: 58/58 raw files, 0 findings
  in bare ACL2; certified-world checks did not run because the sandbox cannot
  acquire the cert-cache entry lock. This is not certification.
- FN_LAPTOP_OK=1 interface_emit --check: 0 findings; world.py --check passed;
  native_program_check passed. The interface view was regenerated.
- secrets_check: 12 files, 0 secret-shaped values; git diff --check passed.
- Lock gate remains RED: 37 new keys against the repository baseline,
  exactly the base revision's set; no lane-added key. The supplied list omits
  `R1b|fnn-extent-executor-actual-return|fnn-cold-worker-phase:unlocked-read`,
  already present in the base. Extent ownership needs that repair; no baseline
  or rule was changed. The base also has five stale callback source locators.
- C must run test_bp_node_native, test_native_host_lifecycle and
  test_native_fence_boundary on the rebuilt native image.

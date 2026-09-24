# GPT-6-Luna feature trial, 2026-09-24

This is a source and review record for three small, independently useful fn
features. The isolated base is `eb2c55fd7b50fee84787dc7380f58ba7c4e3fdea`;
the unresolved cherry-pick in the shared `dev` checkout is outside this trial.
All three implementation lanes use GPT-6-Luna at high reasoning effort. The
reviewer uses GPT-6-Sol. No model token or currency total has been supplied,
so this record does not invent one. Costs below include implementation,
repairs, review, certification and integration work as observed.

| Lane | Intended feature | Acceptance observations |
| --- | --- | --- |
| Web number windows | The loopback human reader offers older/newer links over at most 40 local article *numbers* per request. | A browser can traverse older and newer windows, including a window containing only holes; exact `OVER` ranges remain bounded and a later arrival does not silently move an explicit window. HTTP and NNTP socket tests verify the called path. |
| Offline cursor inspection | Native `consumer-inspect CURSOR.fncu` reads a bounded regular file and invokes the existing ACL2 `fn-cp-cursor-decode`. | Exact 346-octet encoded bound, valid field display, malformed/overbound refusal, and explicit wording that token contents prove no Store currentness, acceptance or processing. No local-control authority is acquired. |
| Local consumer status | Same-UID local-control `consumer status CONTROL ID` asks ACL2 for the registered consumer's committed ACK, committed Store journal frontier and event distance. | ACL2 checks the local principal/query/view scope, derives all three values, and has a bounded distinct FNCT reply. Native CLI prints those values without Store mutation; unknown/scope-mismatched IDs refuse. Called-path and native tests exercise the result. |

Source and tests are separate from image evidence: a passing Python or raw-host
test does not show the feature on a source-matched saved native image. The
shared image run is coordinated by the native qualification lane after the
isolated trial source converges. No change to `/tank/fn/node` is authorized by
this trial.

## Review and integration log

- 02:31 UTC: Reviewer created `lane/luna-feature-review` worktree from the
  isolated base and read the relevant project guide, architecture, milestone,
  decision, working-loop, web and consumer contracts. The three Luna lanes
  supplied planned interfaces before first commits.
- Early web review: numeric anchors must come from the requested window, not
  returned rows, so an all-hole window remains traversable. The lane's working
  diff follows this design and uses socket plus HTTP tests. Requested an
  entirely empty group witness.
- Early cursor review: the decoder allows a 512-octet preflight, but the
  encoder's exact maximum is 346 octets. The lane accepted the correction and
  changed its file-read ceiling to ACL2's existing
  `fn-cpj-max-cursor-octets`, with a 346/347 boundary test planned.
- Early status review: existing FNCT kind-5 replies permit only an accepted
  `fncu` cursor body. The lane changed the plan to a distinct kind-7 fixed
  scalar reply; the consumer Store lane confirmed ACK comes from the durable
  scoped registration and frontier from the committed consumer projection.

Source commits, repairs, test commands, manifests, image revision and final
per-feature disposition will be appended as the packets finish. Reviewer
implementation changes, if any, will be labeled separately.

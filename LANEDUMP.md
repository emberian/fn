# Native history roots — Sol

Base: origin/dev 041fceb1a. Owner: deputy_history. Branch codex/native-history-roots.

Scope: authoritative P3 page history behind installed consumers, snapshot/root ownership, bounded reclaim with honest funding.

Source finding: checkpoint fnn-history-image-build uses fn-his-snapshot -> fn-hrc-load all records -> flush. fn-hrc-flush-step advances lo but leaves old suffix slots retaining every event. fn-his-release resets lo/hi but does not shrink/clear suffix. Existing HEP backing is an independent nested t-row tree with unavailable genuine issuer; connecting it alone would duplicate P3.

First consumer packet: incremental page snapshot construction through append/flush/empty-suffix recycling, used by actual three native publishers. Immutable retained-image verification is Astra S045; synchronized capture funding is Astra S114. Preserve exact image bytes and named refusal. This packet removes proportional suffix retention and one giant suffix load; it does NOT establish bounded reclaim nor authorize lowering fn-orcp-estimate. Fresh logical Store/catalog/history and node lists still allocate proportional copies.

Next: actual fn-hist P3 attachment/open adoption and root publication, joined to private owner carrier (deputy_proof_engineering). fn-host-hist-sync requires exact current history or prefix plus reload marker; authoritative association must carry it.

No claims of completed native/root capability yet. No image build launched. Integration owns convergence runs/dev writes.

Refined quantum scope: fn-his-build-yieldp is ACL2 row-cadence policy, not a work bound. Existing fn-hp-x-append-step encodes whole row and relocates 2*2048*cap(R) words plus O(image) pgs-x-grow-image. Next connected continuation: page-sized readiness/copy/zero/mark before persistent root adoption. No scheduler-blackout elimination claim.

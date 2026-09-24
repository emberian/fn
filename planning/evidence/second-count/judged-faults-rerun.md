| cut | coordinate | table | column | ready / client / owner exit (or cut exit) | at death: txns, staging | recover | candidate | resubmit | verdict |
|---|---|---|---|---|---|---|---|---|---|


cut observations: 0 passed: 0
failures:
fault dev-post-fault-eio {"post": 3, "owner": null, "recover": 0, "first": null, "second": null, "open_post": null, "init": 0, "plain_post": null}
fault dev-owner-post-fault-eio {"post": 3, "owner": 3, "recover": 0, "first": null, "second": null, "open_post": null, "init": 0, "plain_post": null}
fault dev-control-fault {"post": 3, "owner": 3, "recover": 0, "first": null, "second": null, "open_post": null, "init": 0, "plain_post": null}
fault dev-control-test-stop-kill-0 {"post": 3, "owner": -9, "recover": 0, "first": null, "second": null, "open_post": null, "init": 0, "plain_post": null}
fault dev-control-test-stop-kill-1 {"post": 3, "owner": -9, "recover": 0, "first": null, "second": null, "open_post": null, "init": 0, "plain_post": null}
fault dev-control-test-stop-kill-2 {"post": 3, "owner": -9, "recover": 0, "first": null, "second": null, "open_post": null, "init": 0, "plain_post": null}
fault dev-control-test-stop-kill-3 {"post": 3, "owner": -9, "recover": 0, "first": null, "second": null, "open_post": null, "init": 0, "plain_post": null}
fault dev-control-test-stop-kill-4 {"post": 3, "owner": -9, "recover": 0, "first": null, "second": null, "open_post": null, "init": 0, "plain_post": null}
fault cross-entry-retry-store-then-operator {"post": null, "owner": null, "recover": null, "first": 0, "second": 1, "open_post": null, "init": 0, "plain_post": null}
fault cross-entry-retry-operator-then-store {"post": null, "owner": null, "recover": null, "first": 0, "second": 1, "open_post": null, "init": 0, "plain_post": null}
fault dev-allocation-orphans-recover {"post": 0, "owner": 0, "recover": 0, "first": null, "second": null, "open_post": null, "init": 0, "plain_post": null}
fault dev-allocation-orphans-store-post {"post": 1, "owner": 0, "recover": null, "first": null, "second": null, "open_post": 0, "init": 0, "plain_post": null}
fault prod-selectors-refused-at-start {"post": null, "owner": null, "recover": null, "first": null, "second": null, "open_post": null, "init": 0, "plain_post": null}
fault prod-raw-store-post-guard {"post": null, "owner": null, "recover": null, "first": null, "second": null, "open_post": null, "init": null, "plain_post": 5}
fault prod-init-fault {"post": null, "owner": null, "recover": null, "first": null, "second": null, "open_post": null, "init": 5, "plain_post": null}

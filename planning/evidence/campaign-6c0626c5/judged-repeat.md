| cut | coordinate | table | column | ready / client / owner exit (or cut exit) | at death: txns, staging | recover | candidate | resubmit | verdict |
|---|---|---|---|---|---|---|---|---|---|
| `frontier-created` | `fn-bs-frontier-program` | absent | served | ready True / 3 / -9 | 1, .allocation- | 1 1 0 | absent | accepted operator post ACCEPTED rc 0 | PASS |
| `frontier-created` | `fn-bs-frontier-program` | absent | store/recover | -9 | 1, .allocation- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `frontier-written` | `fn-bs-frontier-program` | absent | served | ready True / 3 / -9 | 1, .allocation- | 1 1 0 | absent | accepted operator post ACCEPTED rc 0 | PASS |
| `frontier-written` | `fn-bs-frontier-program` | absent | store/recover | -9 | 1, .allocation- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `frontier-staged-durable` | `fn-bs-frontier-program` | absent | served | ready True / 3 / -9 | 1, .allocation- | 1 1 0 | absent | accepted operator post ACCEPTED rc 0 | PASS |
| `frontier-staged-durable` | `fn-bs-frontier-program` | absent | store/recover | -9 | 1, .allocation- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `frontier-replaced` | `fn-bs-frontier-program` | absent | served | ready True / 3 / -9 | 1, none | 1 1 0 | absent | accepted operator post ACCEPTED rc 0 | PASS |
| `frontier-replaced` | `fn-bs-frontier-program` | absent | store/recover | -9 | 1, none | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `frontier-attempted` | `fn-bs-frontier-program` | absent | served | ready True / 3 / -9 | 1, none | 1 1 0 | absent | accepted operator post ACCEPTED rc 0 | PASS |
| `frontier-attempted` | `fn-bs-frontier-program` | absent | store/recover | -9 | 1, none | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `frontier-durable` | `fn-bs-frontier-program` | absent | served | ready True / 3 / -9 | 1, none | 1 1 0 | absent | accepted operator post ACCEPTED rc 0 | PASS |
| `frontier-durable` | `fn-bs-frontier-program` | absent | store/recover | -9 | 1, none | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `frontier-reserved` | `fn-bs-frontier-program` | absent | served | ready True / 3 / -9 | 1, none | 1 1 0 | absent | accepted operator post ACCEPTED rc 0 | PASS |
| `frontier-reserved` | `fn-bs-frontier-program` | absent | store/recover | -9 | 1, none | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `record-created` | `fn-bs-record-program` | absent | served | ready True / 3 / -9 | 1, .stage- | 1 1 0 | absent | accepted operator post ACCEPTED rc 0 | PASS |
| `record-created` | `fn-bs-record-program` | absent | store/recover | -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `record-written` | `fn-bs-record-program` | absent | served | ready True / 3 / -9 | 1, .stage- | 1 1 0 | absent | accepted operator post ACCEPTED rc 0 | PASS |
| `record-written` | `fn-bs-record-program` | absent | store/recover | -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `record-staged-durable` | `fn-bs-record-program` | absent | served | ready True / 3 / -9 | 1, .stage- | 1 1 0 | absent | accepted operator post ACCEPTED rc 0 | PASS |
| `record-staged-durable` | `fn-bs-record-program` | absent | store/recover | -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `record-linked` | `fn-bs-record-program` | either | served | ready True / 3 / -9 | 2, .stage- | 2 2 0 | present | accepted operator post DUPLICATE rc 0 | PASS |
| `record-linked` | `fn-bs-record-program` | either | store/recover | -9 | 2, .stage- | 2 2 0 | present | duplicate rc 0 | PASS |
| `record-attempted` | `fn-bs-record-program` | present | served | ready True / 3 / -9 | 2, .stage- | 2 2 0 | present | accepted operator post DUPLICATE rc 0 | PASS |
| `record-attempted` | `fn-bs-record-program` | present | store/recover | -9 | 2, .stage- | 2 2 0 | present | duplicate rc 0 | PASS |
| `record-durable` | `fn-bs-record-program` | present | served | ready True / 3 / -9 | 2, .stage- | 2 2 0 | present | accepted operator post DUPLICATE rc 0 | PASS |
| `record-durable` | `fn-bs-record-program` | present | store/recover | -9 | 2, .stage- | 2 2 0 | present | duplicate rc 0 | PASS |
| `record-completing` | `fn-bs-record-program` | present | served | ready True / 3 / -9 | 2, .stage- | 2 2 0 | present | accepted operator post DUPLICATE rc 0 | PASS |
| `record-completing` | `fn-bs-record-program` | present | store/recover | -9 | 2, .stage- | 2 2 0 | present | duplicate rc 0 | PASS |
| `record-stage-unlinked` | `fn-bs-record-program` | present | served | ready True / 3 / -9 | 2, none | 2 2 0 | present | accepted operator post DUPLICATE rc 0 | PASS |
| `record-stage-unlinked` | `fn-bs-record-program` | present | store/recover | -9 | 2, none | 2 2 0 | present | duplicate rc 0 | PASS |
| `record-staging-cleaned` | `fn-bs-record-program` | present | served | ready True / 3 / -9 | 2, none | 2 2 0 | present | accepted operator post DUPLICATE rc 0 | PASS |
| `record-staging-cleaned` | `fn-bs-record-program` | present | store/recover | -9 | 2, none | 2 2 0 | present | duplicate rc 0 | PASS |
| `finish-consumed` | `fn-bs-finish-program` | present | served | ready True / 3 / -9 | 2, none | 2 2 0 | present | accepted operator post DUPLICATE rc 0 | PASS |
| `finish-consumed` | `fn-bs-finish-program` | present | store/recover | -9 | 2, none | 2 2 0 | present | duplicate rc 0 | PASS |
| `finish-durable` | `fn-bs-finish-program` | present | served | ready True / 3 / -9 | 2, none | 2 2 0 | present | accepted operator post DUPLICATE rc 0 | PASS |
| `finish-durable` | `fn-bs-finish-program` | present | store/recover | -9 | 2, none | 2 2 0 | present | duplicate rc 0 | PASS |
| `recover-replayed` | `fn-bs-recover-program` | n/a | served | ready False / - / -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recover-replayed` | `fn-bs-recover-program` | n/a | store/recover | -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recover-barrier-1` | `fn-bs-recover-program` | n/a | served | ready False / - / -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recover-barrier-1` | `fn-bs-recover-program` | n/a | store/recover | -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recover-barrier-2` | `fn-bs-recover-program` | n/a | served | ready False / - / -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recover-barrier-2` | `fn-bs-recover-program` | n/a | store/recover | -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recover-barrier-3` | `fn-bs-recover-program` | n/a | served | ready False / - / -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recover-barrier-3` | `fn-bs-recover-program` | n/a | store/recover | -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recover-barrier-4` | `fn-bs-recover-program` | n/a | served | ready False / - / -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recover-barrier-4` | `fn-bs-recover-program` | n/a | store/recover | -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recover-barrier-5` | `fn-bs-recover-program` | n/a | served | ready False / - / -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recover-barrier-5` | `fn-bs-recover-program` | n/a | store/recover | -9 | 1, .stage- | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recovery-stage-unlinked` | `fn-bs-recover-stage-cleanup-program after fn-bs-recover-program` | n/a | served | ready False / - / -9 | 1, none | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |
| `recovery-stage-unlinked` | `fn-bs-recover-stage-cleanup-program after fn-bs-recover-program` | n/a | store/recover | -9 | 1, none | 1 1 0 | absent | committed sequence=1 charge=2 rc 0 | PASS |

cut observations: 50 passed: 50 (failing observations are counted per cut and column)
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

| cut | action | table | NNTP reply | owner exit | candidate after | prior reread | candidate reread | repost reply |
|---|---|---|---|---|---|---|---|---|
| frontier-created | kill | absent | `(closed, no reply)` | -9 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-created | eio | absent | `441 posting failed; the store could not write the article, nothing was stored` | 0 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-written | kill | absent | `(closed, no reply)` | -9 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-written | eio | absent | `441 posting failed; the store could not write the article, nothing was stored` | 0 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-staged-durable | kill | absent | `(closed, no reply)` | -9 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-staged-durable | eio | absent | `441 posting failed; the store could not write the article, nothing was stored` | 0 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-replaced | kill | absent | `(closed, no reply)` | -9 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-replaced | eio | absent | `441 posting failed; the outcome is uncertain, do not repost` | 3 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-attempted | kill | absent | `(closed, no reply)` | -9 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-attempted | eio | absent | `441 posting failed; the outcome is uncertain, do not repost` | 3 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-durable | kill | absent | `(closed, no reply)` | -9 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-durable | eio | absent | `441 posting failed; the outcome is uncertain, do not repost` | 3 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-reserved | kill | absent | `(closed, no reply)` | -9 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| frontier-reserved | eio | absent | `441 posting failed; the outcome is uncertain, do not repost` | 3 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| record-created | kill | absent | `(closed, no reply)` | -9 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| record-created | eio | absent | `441 posting failed; the store could not write the article, nothing was stored` | 0 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| record-written | kill | absent | `(closed, no reply)` | -9 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| record-written | eio | absent | `441 posting failed; the store could not write the article, nothing was stored` | 0 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| record-staged-durable | kill | absent | `(closed, no reply)` | -9 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| record-staged-durable | eio | absent | `441 posting failed; the store could not write the article, nothing was stored` | 0 | absent | True/True | n/a (1 / 430) | `240 article received OK` |
| record-linked | kill | either | `(closed, no reply)` | -9 | present | True/True | True/True/True | `441 posting failed; this article is already stored here` |
| record-linked | eio | either | `441 posting failed; the outcome is uncertain, do not repost` | 3 | present | True/True | True/True/True | `441 posting failed; a different article with this Message-ID is stored here` |
| record-attempted | kill | present | `(closed, no reply)` | -9 | present | True/True | True/True/True | `441 posting failed; a different article with this Message-ID is stored here` |
| record-attempted | eio | present | `441 posting failed; the outcome is uncertain, do not repost` | 3 | present | True/True | True/True/True | `441 posting failed; this article is already stored here` |
| record-durable | kill | present | `(closed, no reply)` | -9 | present | True/True | True/True/True | `441 posting failed; a different article with this Message-ID is stored here` |
| record-durable | eio | present | `441 posting failed; the outcome is uncertain, do not repost` | 3 | present | True/True | True/True/True | `441 posting failed; this article is already stored here` |
| record-completing | kill | present | `(closed, no reply)` | -9 | present | True/True | True/True/True | `441 posting failed; this article is already stored here` |
| record-completing | eio | present | `441 posting failed; the outcome is uncertain, do not repost` | 3 | present | True/True | True/True/True | `441 posting failed; a different article with this Message-ID is stored here` |
| record-stage-unlinked | kill | present | `(closed, no reply)` | -9 | present | True/True | True/True/True | `441 posting failed; this article is already stored here` |
| record-stage-unlinked | eio | present | `240 article received OK` | 0 | present | True/True | True/True/True | `441 posting failed; a different article with this Message-ID is stored here` |
| record-staging-cleaned | kill | present | `(closed, no reply)` | -9 | present | True/True | True/True/True | `441 posting failed; a different article with this Message-ID is stored here` |
| record-staging-cleaned | eio | present | `441 posting failed; the outcome is uncertain, do not repost` | 3 | present | True/True | True/True/True | `441 posting failed; this article is already stored here` |
| finish-consumed | kill | present | `(closed, no reply)` | -9 | present | True/True | True/True/True | `441 posting failed; a different article with this Message-ID is stored here` |
| finish-consumed | eio | present | `441 posting failed; the outcome is uncertain, do not repost` | 3 | present | True/True | True/True/True | `441 posting failed; this article is already stored here` |
| finish-durable | kill | present | `(closed, no reply)` | -9 | present | True/True | True/True/True | `441 posting failed; this article is already stored here` |
| finish-durable | eio | present | `441 posting failed; the outcome is uncertain, do not repost` | 3 | present | True/True | True/True/True | `441 posting failed; a different article with this Message-ID is stored here` |
| dev-accepted-then-sigkill | fn-host-developer | - | `240 article received OK` | -9 | present | True/True | True/True/True | `441 posting failed; this article is already stored here` |
| dev-refused-no-from | fn-host-developer | - | `441 posting failed; From is required` | 0 | absent | True/True | n/a (1 / 430) | `441 posting failed; From is required` |
| prod-accepted-then-sigkill | fn-host | - | `240 article received OK` | -9 | present | True/True | True/True/True | `441 posting failed; a different article with this Message-ID is stored here` |
| prod-sigkill-mid-article | fn-host | - | `(closed, no reply)` | -9 | absent | True/True | n/a (1 / 430) | `-` |

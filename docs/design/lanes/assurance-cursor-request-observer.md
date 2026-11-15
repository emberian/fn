# Cursor response source observation

The cursor's SELECT arm acquires a request endpoint before parsing or starting
any READ or ARTICLE working lease. RX/TX already belong to its connection and
are baseline actor resources. Endpoint geometry is the shared actual
`fn2-c-source-request-endpoint(readRows, successorRows, cursorRow)`; no fixed
request count or extra endpoint table is introduced.

The real cursor row stores the monotonically issued receipt. Admission validates
its SELECT phase and generation, then atomically binds both derived READ rows
before returning. A failed pair preflight rolls back a newly acquired request
observation within the same call. READ key/release operations retain their
parent binding. An authenticated held parent permits a new child READ while the
writer is PENDING, so an existing response can enumerate another page without
deadlocking the waiting writer. EXCLUSIVE/UNCERTAIN still refuse new children.

FINISH releases both transient READs and the ARTICLE lease. DRAINING requires
cursor pending=0, TURN=1, and lease=NONE before clearing both child bindings and
releasing the request endpoint. Normal connection SEND completion returns TURN;
the connection's cancellation callback sets CANCEL and TURN only in its draining
arm after connection pending/borrows are zero. Request receipt clear and cursor
generation advance occur after the exact release. A response does not release
its observation merely because one READ or page ended.

All ten cursor READ-start sites route blocked `:more` as bounded runnable work.
Five lookup/identity sites already did so; five range/scan starts now do too.
These source changes are not activated or ACL2 admitted. Six cursor source
controls and the READ/geometry source controls were run; no ACL2/runtime compute
was performed. Source observer invariant and nested-PENDING fixture obligations
remain the shared provider's prepared, unexecuted evidence.

# Native BP contact window, selected packet

The native caller `host/native/bp-contact.lisp:35` calls
`fn-bpsc-contact-decision` and `fn-bpsc-contact-event` from
`books/bp-contact-service.lisp`, then sends the returned event through
`fnn-bps-step` and the shared durable effect driver. It advances `:clock`
before consulting ready peers. An open contact is possible only for the
window's exact ready peer inside its inclusive monotonic interval; a closed
window emits a close event. The sender's TCPCL result stays accepted,
refused, or uncertain in the shared service. No carrier result releases an
application pin.

`fn-bpsc-open-needs-ready-peer-and-window` proves the opening preconditions
from the decision actually called by the host. The event equivalence and
invalid-event theorems connect that decision to the host's `:contact` event.
`tests/acl2/bp-contact-service-tests.lisp` provides a reachable open contact,
wrong-peer, absent-ready-peer, outside-window, and malformed-window witnesses.

Selected certification: `python3 tools/farm.py --root
/Users/ember/dev/fn/build/lanes/bp-contact-service --remote-root
/home/ember/fn-gates/takeover-bp-contact-service --acl2
/home/ember/fn-gates/toolchains/w25/acl2-literal --jobs 2
--timeout-seconds 90 submit persvati books/bp-contact-service
tests/acl2/bp-contact-service-tests`. Run `run-20260923T184515Z-8217` passed;
the [manifest](manifests/certify-20260923T184517Z-2905271.json) records
ACL2 8.7 / SBCL 2.6.8, the source digests, 14 cached dependencies, two
certified roots, 1.626 and 1.115 seconds per root, and 2.747 seconds total
certificate wall time. An earlier bounded run found an opening-theorem rule
class error; it was fixed before this successful run.

`python3 -m py_compile tests/test_bp_contact_native.py` passed, and SBCL
parsed all seven raw host forms. `make check` reaches only the generated
ledger staleness failure after this new book/root; root owns ledger
regeneration on integration. The native image test is written but not yet
run: a new shared A2 image is needed. The packet is a one-peer finite contact
runner, not a multi-peer fairness theorem or the two-node receipt gate.

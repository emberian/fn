"""Bridge validated local journal fields into the same live ACL2 workflow model."""
from tools.run_store import Acl2Store, acl2_boolean, acl2_result, acl2_symbol
from tools.workflow_journal import JournalFault
from tools.workflow_journal import encode_record

_FIXED = {"config": ":config", "enqueue": ":enqueue", "attempt": ":attempt",
          "transport": ":transport", "receipt-intent": ":receipt-intent"}
_FIXED["outcome"] = ":outcome"
_FIXED["retry-request"] = ":retry-request"
_ORDER = {
 "config": ("local-eid","peer-eid","policy-id","receipt-authority","bp-lifetime","incarnation","authorization-context"),
 "enqueue": ("txid","tx-generation","work-id","msgid","immutable-subject","archive-obligation-id","forward-obligation-id","peer-eid","policy-id","terms-id"),
 "attempt": ("txid","tx-generation","work-id","attempt-id","attempt-generation","local-eid","peer-eid","policy-id","bp-lifetime"),
 "transport": ("work-id","attempt-id","attempt-generation","status"),
 "receipt-intent": ("txid","tx-generation","receipt-id","work-id","immutable-subject","issuer-eid","peer-eid","policy-id","incarnation","authorization-context","terms-id")}
_ORDER["outcome"] = ("txid", "tx-generation", "phase", "result")
_ORDER["retry-request"] = ("work-id", "attempt-id", "attempt-generation", "policy-id")

def _string(value):
    raw=value.encode("utf-8","strict")
    return "(fn-store-octets->string '("+" ".join(map(str,raw))+"))"
def _value(name, value):
    if isinstance(value,int) and not isinstance(value,bool): return str(value)
    if name in {"status", "phase", "result"}: return ":"+value
    return _string(value)
def records_form(records):
    rows=[]
    for kind, values in records:
        encode_record(kind, values)
        if kind not in _ORDER or set(values) != set(_ORDER[kind]):
            raise JournalFault("ACL2 bridge record shape")
        rows.append("(list "+_FIXED[kind]+" "+" ".join(_value(n,values[n]) for n in _ORDER[kind])+")")
    return "(list "+" ".join(rows)+")"
def record_form(record):
    return records_form((record,))[6:-1]

class Acl2WorkflowReplay:
    """Uses an Acl2Store session so workflow replay sees its recovered node."""
    def __init__(self, store: Acl2Store):
        self.store=store
        self.initialized=False
        store.call('(ld "host/workflow-host.lisp" :ld-error-action :return :ld-error-triples t)')
    def __call__(self, records):
        if not records:
            self.initialized=False
            return self
        outcome=acl2_symbol(self.store.call("(fn-workflow-install-replay "+records_form(records)+" state)"))
        if outcome != "ready": raise JournalFault("ACL2 rejected workflow journal")
        self.initialized=True
        return self
    def fenced(self):
        return acl2_boolean(self.store.call("(fn-workflow-fencedp state)"))
    def work_status(self, work_id):
        raw=acl2_result(self.store.call("(fn-workflow-work-status "+_string(work_id)+" state)")).lower()
        if not raw.startswith(b":"): raise JournalFault("ACL2 returned invalid workflow status")
        return raw[1:].decode("ascii")
    def preflight(self, record):
        return acl2_symbol(self.store.call("(fn-workflow-preflight-record "+
                           record_form(record)+" state)")) == "ready"
    def history_preflight(self, records):
        return acl2_symbol(self.store.call("(fn-workflow-preflight-history "+
                           records_form(records)+" state)")) == "ready"
    def apply_record(self, record):
        outcome=acl2_symbol(self.store.call("(fn-workflow-apply-record "+
                            record_form(record)+" state)"))
        if outcome != "ready": raise JournalFault("ACL2 rejected durable workflow record")
    def take_submit(self, values):
        form="(fn-workflow-take-submit "+_string(values["work-id"])+" "+\
             _string(values["attempt-id"])+" "+str(values["attempt-generation"])+" state)"
        return acl2_boolean(self.store.call(form))

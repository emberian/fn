"""Safe fixed-form bridge from receiver journal bytes into executable ACL2 fn-bpr."""
from tools.run_store import Acl2Store, acl2_boolean, acl2_octets, acl2_symbol
from tools.workflow_journal import JournalFault
from tools.receipt_journal import MAX_BLOB, MAX_TEXT, encode_receiver_record
ORDER={"config":("destination-eid","policy-id","issuer-eid"),
 "request-context":("inbound-bid","request-adu","store-record","policy-authorized"),
 "receipt-intent":("work-id","receipt-id","receipt-adu","policy-authorized"),
 "receipt-decision":("work-id","receipt-id","outcome")}
def _octets(v):
 if not isinstance(v,bytes) or not 1<=len(v)<=MAX_BLOB: raise JournalFault("receiver bridge octet bound")
 return "'(\u0020"+" ".join(str(x) for x in v)+")"
def _string(v):
 if not isinstance(v,str): raise JournalFault("receiver bridge text type")
 raw=v.encode('utf-8','strict')
 if not 1<=len(raw)<=MAX_TEXT: raise JournalFault("receiver bridge text bound")
 return "(fn-store-octets->string "+_octets(raw)+")"
def record_form(record):
 kind,v=record
 encode_receiver_record(kind,v)
 if kind not in ORDER or set(v)!=set(ORDER[kind]): raise JournalFault("receiver bridge shape")
 xs=[]
 for n in ORDER[kind]:
  x=v[n]
  if n in {"request-adu","store-record","receipt-adu"}:xs.append(_octets(x))
  elif n=="policy-authorized":
   if x is not True: raise JournalFault("receiver bridge policy")
   xs.append("t")
  elif n=="outcome":
   if x not in {"committed","absent"}: raise JournalFault("receiver bridge outcome")
   xs.append(":"+x)
  else:xs.append(_string(x))
 return "(list :"+kind+" "+" ".join(xs)+")"
def records_form(records): return "(list "+" ".join(record_form(r) for r in records)+")"
class Acl2ReceiptBridge:
 def __init__(self,store:Acl2Store):
  self.store=store;self.initialized=False
  store.call('(ld "host/bp-receipt-journal-host.lisp" :ld-error-action :return :ld-error-triples t)')
 def replay(self,records):
  if not records:self.initialized=False;return self
  if acl2_symbol(self.store.call("(fn-bprj-install "+records_form(records)+" state)"))!="ready": raise JournalFault("ACL2 rejected receiver journal")
  self.initialized=True;return self
 def valid_config(self,record): return acl2_boolean(
  self.store.call("(fn-bprj-valid-config "+record_form(record)+" state)"))
 def preflight(self,record): return acl2_symbol(self.store.call("(fn-bprj-preflight "+record_form(record)+" state)"))=="ready"
 def apply(self,record):
  if acl2_symbol(self.store.call("(fn-bprj-apply "+record_form(record)+" state)"))!="ready": raise JournalFault("ACL2 rejected durable receiver record")
 def preview_receipt(self,work_id,receipt_id):
  return acl2_octets(self.store.call("(fn-bprj-preview-receipt "+_string(work_id)+" "+_string(receipt_id)+" state)"))
 def receipt_adu(self,request_adu): return acl2_octets(self.store.call("(fn-bprj-receipt-adu "+_octets(request_adu)+" state)"))

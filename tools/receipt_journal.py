"""Separate durable receiver request/receipt journal; ACL2 owns semantics."""
from __future__ import annotations
import fcntl, hashlib, os, struct
from pathlib import Path
from tools.workflow_journal import (FaultPoints, JournalError, JournalFault, JournalUncertain,
                                    NO_FAULTS, durable_barrier, fsync_dir,
                                    open_exclusive_lock, read_regular_barriered, write_all)
MAGIC=b"FNRJ"; SCHEMA=1; MAX_TEXT=512; MAX_BLOB=131072; MAX_RECORD=270000
MAX_RECORDS=4096; MAX_AGGREGATE=64*1024*1024
KINDS={"config":1,"request-context":2,"receipt-intent":3,"receipt-decision":4}
NAMES={v:k for k,v in KINDS.items()}
FIELDS={
 "config":(("destination-eid","text"),("policy-id","text"),("issuer-eid","text")),
 "request-context":(("inbound-bid","text"),("request-adu","blob"),("store-record","blob"),("policy-authorized","true")),
 "receipt-intent":(("work-id","text"),("receipt-id","text"),("receipt-adu","blob"),("policy-authorized","true")),
 "receipt-decision":(("work-id","text"),("receipt-id","text"),("outcome","outcome"))}
OUTCOMES={"committed":1,"absent":2}
def _s(v):
 if not isinstance(v,str): raise JournalError("receiver text type")
 b=v.encode("utf-8","strict")
 if not 1<=len(b)<=MAX_TEXT: raise JournalError("receiver text bound")
 return struct.pack(">H",len(b))+b
def _b(v):
 if not isinstance(v,bytes) or not 1<=len(v)<=MAX_BLOB: raise JournalError("receiver blob bound")
 return struct.pack(">I",len(v))+v
def encode_receiver_record(kind,values):
 if kind not in FIELDS or set(values)!={n for n,_ in FIELDS[kind]}: raise JournalError("receiver record shape")
 p=bytearray()
 for n,t in FIELDS[kind]:
  v=values[n]
  if t=="text":p+=_s(v)
  elif t=="blob":p+=_b(v)
  elif t=="true":
   if v is not True: raise JournalError("receiver policy decision")
   p.append(1)
  else:
   if v not in OUTCOMES: raise JournalError("receiver outcome")
   p.append(OUTCOMES[v])
 h=MAGIC+bytes((SCHEMA,KINDS[kind]))+struct.pack(">I",len(p)); raw=h+p+hashlib.sha256(h+p).digest()
 if len(raw)>MAX_RECORD: raise JournalError("receiver record bound")
 return bytes(raw)
def decode_receiver_record(raw):
 if not 42<=len(raw)<=MAX_RECORD or raw[:4]!=MAGIC or raw[4]!=SCHEMA: raise JournalFault("receiver frame")
 if hashlib.sha256(raw[:-32]).digest()!=raw[-32:]: raise JournalFault("receiver checksum")
 kind=NAMES.get(raw[5]); size=struct.unpack(">I",raw[6:10])[0]
 if kind is None or size!=len(raw)-42: raise JournalFault("receiver kind/length")
 p=memoryview(raw)[10:-32]; o=0; values={}; rev={v:k for k,v in OUTCOMES.items()}
 for n,t in FIELDS[kind]:
  if t=="text":
   if o+2>len(p): raise JournalFault("receiver text")
   z=struct.unpack(">H",p[o:o+2])[0];o+=2
   if not 1<=z<=MAX_TEXT or o+z>len(p): raise JournalFault("receiver text bound")
   try: values[n]=bytes(p[o:o+z]).decode("utf-8","strict")
   except UnicodeDecodeError as e: raise JournalFault("receiver utf8") from e
   o+=z
  elif t=="blob":
   if o+4>len(p): raise JournalFault("receiver blob")
   z=struct.unpack(">I",p[o:o+4])[0];o+=4
   if not 1<=z<=MAX_BLOB or o+z>len(p): raise JournalFault("receiver blob bound")
   values[n]=bytes(p[o:o+z]);o+=z
  else:
   if o>=len(p): raise JournalFault("receiver enum")
   q=int(p[o]);o+=1
   if t=="true":
    if q!=1: raise JournalFault("receiver policy")
    values[n]=True
   else:
    if q not in rev: raise JournalFault("receiver outcome")
    values[n]=rev[q]
 if o!=len(p): raise JournalFault("receiver trailing bytes")
 return kind,values
class ReceiptJournal:
 def __init__(self,root,bridge,faults:FaultPoints=NO_FAULTS):
  self.root=Path(root);self.records=self.root/"records";self.staging=self.root/"staging"
  self.bridge=bridge;self.fenced=True
  self.lock_fd=None;self.faults=faults
 def open(self):
  self.fenced=True
  if self.lock_fd is not None: raise JournalFault("receiver journal already open")
  self.root.mkdir(parents=True,mode=0o700,exist_ok=True)
  self.lock_fd=open_exclusive_lock(self.root/"receipt.lock","receiver")
  try:
   self.records.mkdir(mode=0o700,exist_ok=True);self.staging.mkdir(mode=0o700,exist_ok=True);fsync_dir(self.root);fsync_dir(self.root.parent)
   entries=sorted(self.records.iterdir()); total=0; decoded=[]
   if len(entries)>MAX_RECORDS: raise JournalFault("receiver count")
   for i,p in enumerate(entries):
    if p.name!=f"{i:016x}.rj": raise JournalFault("receiver namespace")
    data=read_regular_barriered(p,MAX_RECORD);total+=len(data)
    if total>MAX_AGGREGATE: raise JournalFault("receiver aggregate")
    decoded.append(decode_receiver_record(data))
   fsync_dir(self.records);self.bridge.replay(tuple(decoded));self.fenced=False;return self.bridge
  except Exception as e:
   self.close()
   if isinstance(e,(JournalError,JournalFault,JournalUncertain)):raise
   raise JournalFault("receiver recovery failed") from e
 def close(self):
  self.fenced=True
  if self.lock_fd is not None:
   fcntl.flock(self.lock_fd,fcntl.LOCK_UN);os.close(self.lock_fd);self.lock_fd=None
 def publish(self,kind,values,reserve_resolution=False):
  if self.fenced: raise JournalFault("receiver journal fenced")
  raw=encode_receiver_record(kind,values); record=(kind,values)
  if kind=="config":
   if list(self.records.iterdir()): raise JournalFault("receiver journal already initialized")
   if not self.bridge.valid_config(record): raise JournalError("ACL2 rejected receiver config before publication")
  elif not self.bridge.preflight(record): raise JournalError("ACL2 rejected receiver record before publication")
  entries=list(self.records.iterdir());total=sum(p.stat().st_size for p in entries)
  reserve=MAX_RECORD if reserve_resolution else 0; slots=2 if reserve_resolution else 1
  if len(entries)+slots>MAX_RECORDS or total+len(raw)+reserve>MAX_AGGREGATE: raise JournalFault("receiver resolution headroom")
  seq=len(entries);tmp=self.staging/f"{seq:016x}.{os.getpid()}.tmp";final=self.records/f"{seq:016x}.rj"
  fd=os.open(tmp,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600);attempted=False
  try:
   write_all(fd,raw);durable_barrier(fd)
   # Retire the descriptor number before closing: a failing close may already
   # have released it, and closing again would close an unrelated descriptor.
   handle,fd=fd,-1
   os.close(handle);attempted=True;os.link(tmp,final)
   self.faults.at("postlink")
   fsync_dir(self.records)
  except Exception as e:
   if fd>=0:os.close(fd)
   if attempted:self.fenced=True;raise JournalUncertain("receiver publication uncertain") from e
   raise
  finally:
   try:tmp.unlink()
   except OSError:pass
  try:
   if kind=="config": self.bridge.replay((record,))
   else: self.bridge.apply(record)
  except Exception:self.fenced=True;raise
  return final
 def initialize(self,values): return self.publish("config",values)
 def persist_request(self,values): return self.publish("request-context",values)
 def accept_request(self,inbound_bid,request_adu,store_record,policy_authorized=True):
  return self.persist_request({"inbound-bid":inbound_bid,"request-adu":request_adu,
   "store-record":store_record,"policy-authorized":policy_authorized})
 def persist_receipt_intent(self,work_id,receipt_id):
  adu=self.bridge.preview_receipt(work_id,receipt_id)
  return self.publish("receipt-intent",{"work-id":work_id,"receipt-id":receipt_id,"receipt-adu":adu,"policy-authorized":True},reserve_resolution=True)
 def prepare_receipt(self,work_id,receipt_id):
  return self.persist_receipt_intent(work_id,receipt_id)
 def decide_receipt(self,work_id,receipt_id,outcome):
  return self.publish("receipt-decision",{"work-id":work_id,"receipt-id":receipt_id,"outcome":outcome})
 def commit_receipt(self,work_id,receipt_id,outcome="committed"):
  return self.decide_receipt(work_id,receipt_id,outcome)
 def receipt_adu(self,request_adu):
  if self.fenced: raise JournalFault("receiver journal fenced")
  return self.bridge.receipt_adu(request_adu)

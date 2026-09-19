"""Separate durable receiver request/receipt journal; ACL2 owns semantics."""
from __future__ import annotations
import fcntl, os
from pathlib import Path
from tools import frame_bridge
from tools.workflow_journal import (FaultPoints, JournalError, JournalFault, JournalUncertain,
                                    NO_FAULTS, durable_barrier, fsync_dir,
                                    open_exclusive_lock, read_regular_barriered, write_all)
MAGIC=b"FNRJ"; SCHEMA=1; MAX_TEXT=512; MAX_BLOB=131072; MAX_RECORD=270000
MAX_RECORDS=4096; MAX_AGGREGATE=64*1024*1024
# The receiver record kinds, their field names and types, and the outcome
# enumeration live in `books/frame`; `frame_bridge` asks for the schema of a
# kind and caches it.  This module keeps no copy of any of them.
def encode_receiver_record(kind,values,bridge=None):
 """`books/frame` builds the record; the host appends the trailer only."""
 try: return frame_bridge.session(bridge).record_frame("receipt",kind,values)
 except frame_bridge.BridgeError as error: raise JournalError(str(error)) from error
def decode_receiver_record(raw,bridge=None):
 """`books/frame` parses the record and compares the host's digest."""
 try: return frame_bridge.session(bridge).record_unframe("receipt",raw)
 except (frame_bridge.BridgeError,UnicodeDecodeError) as error: raise JournalFault(str(error)) from error
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
   self.faults.at("receipt-staged-durable")
   # Retire the descriptor number before closing: a failing close may already
   # have released it, and closing again would close an unrelated descriptor.
   handle,fd=fd,-1
   os.close(handle);attempted=True;os.link(tmp,final)
   self.faults.at("postlink")
   fsync_dir(self.records)
   self.faults.at("receipt-durable")
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
  self.faults.at("receipt-applied")
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

#!/usr/bin/env python3
"""Bind the actual archive worker class to its active/pending control carrier."""
from pathlib import Path
import lisp_rewrite as lr
B=Path(__file__).resolve().parents[1]/'books'
def node(s,p):return lr.match(p,lr.parse(s).forms,deep=False)[0].node
def raw(s,n):return s[n.start:n.end]
def transform(producer,work,control):
 owner=node(control,'(defun fn2-event-archive-ownerp ?*body)')
 ownertext=raw(control,owner)
 child=node(control,'(fn2-sealer-child fn2-core-event-archive ?*body)')
 childtext=raw(control,child)
 control=lr.write(control,[(owner.start,owner.end,''),(child.start,child.end,'')])
 producer=producer.replace('(include-book "event-read-verify")','(include-book "event-read-verify")\n(include-book "event-archive-state")')
 marker='(fn2-book-layer :c)';producer=producer.replace(marker,marker+'\n'+childtext,1)
 old=node(work,'(defun fn2-event-archive-builderp ?*body)')
 new=raw(work,old)
 new=new.replace('(defun fn2-event-archive-builderp (','(defun fn2-event-archive-builderp (fn2-event-archive ',1)
 new=new.replace(':stobjs (',':stobjs (fn2-event-archive ',1)
 new=new.replace(':guard (and ',':guard (and (fn2-event-archive-wfp fn2-event-archive) ',1)
 new=new.replace('(fn2-event-archive-sourcep ', '(fn2-event-archive-ownerp 1 fn2-event-archive ',1)
 oldschema='(equal (fn2-run-builds-schema *fn2-checkpoint-source-build* fn2-run-builds) *fn2-event-archive-schema*)'
 newschema='''(or (and (equal (fn2-run-builds-schema *fn2-checkpoint-source-build* fn2-run-builds) *fn2-event-archive-schema*)
               (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-members*))
          (and (equal (fn2-run-builds-schema *fn2-checkpoint-source-build* fn2-run-builds) 10)
               (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-manifest*)))'''
 if new.count(oldschema)!=1:raise ValueError('archive builder schema guard drift')
 new=new.replace(oldschema,newschema)
 work=lr.write(work,[(old.start,old.end,ownertext+'\n\n'+new)])
 # One readonly control carrier at every actual worker entry and call.
 edits=[]
 for match in lr.match('(fn2-event-archive-operation ?name ?children ?outputs ?*body)',lr.parse(work).forms,deep=False):
  children=match.captures['children'];edits.append((children.start+1,children.start+1,'fn2-event-archive '))
 for match in lr.match('(fn2-event-archive-builderp ?*args)',lr.parse(work).forms):
  args=match.captures['args'];call=match.node
  edits.append((call.items[1].start,call.items[1].start,'fn2-event-archive '))
 work=lr.write(work,edits)
 edits=[]
 for match in lr.match('(fn2-event-archive-builderp ?*args)',lr.parse(control).forms):
  call=match.node;edits.append((call.items[1].start,call.items[1].start,'fn2-event-archive '))
 control=lr.write(control,edits)
 return producer,work,control
if __name__=='__main__':
 names=['event-archive-producer.lisp','event-archive-work.lisp','event-archive-control.lisp']
 values=transform(*[(B/n).read_text() for n in names])
 for n,s in zip(names,values):(B/n).write_text(s)

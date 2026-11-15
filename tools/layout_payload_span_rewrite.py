"""Exact byte-fuel opaque span optimization of the generated scan class.

Apply to the qualified layout source, not the quarantined full-face rewrite.
The list/model scan and every public interface remain unchanged. A chunk
consumes its byte count, so STEP's code/next/continuation keep their meaning.
"""
import lisp_rewrite as lr

SUPPORT = '''; Opaque payload bytes carry a Ref: BYTE does not inspect their contents.
; The logical type test retains old malformed-source behavior. Guarded native
; execution already carries the stobj recognizer, so no whole-pool scan runs.
(defun fn2-layout-payload-chunk (active fuel pos size next end slot gen okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool
                 :guard (and (fn2-pool-wfp fn2-pool) (booleanp active)
                             (natp fuel) (natp pos) (natp size) (natp next) (natp end))))
 (if (and active (posp fuel) (natp pos) (natp size) (< pos size)
          (unsigned-byte-p 32 next) (unsigned-byte-p 32 end) (< next end)
          (mbe :logic (fn2-poolp fn2-pool) :exec t))
     (let ((n (min fuel (- size pos) (- end next))))
       (if (eq (fn2-layout-range-code slot gen next (+ next n) nil okind oslot ogen fn2-pool) :ok)
           n 1))
   1))
(defthm fn2-layout-payload-chunk-positive
 (posp (fn2-layout-payload-chunk active fuel pos size next end slot gen okind oslot ogen fn2-pool))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn2-layout-payload-chunk))))
(defthm fn2-layout-payload-chunk-fuel
 (implies (posp fuel)
  (<= (fn2-layout-payload-chunk active fuel pos size next end slot gen okind oslot ogen fn2-pool) fuel))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn2-layout-payload-chunk))))
(defthm fn2-layout-payload-chunk-untyped-source
 (implies (not (fn2-poolp fn2-pool))
  (equal (fn2-layout-payload-chunk active fuel pos size next end slot gen okind oslot ogen fn2-pool) 1))
 :hints (("Goal" :in-theory (enable fn2-layout-payload-chunk))))
(defthm fn2-layout-byte-payload-chunk-unfolds
 (implies (and (natp pos) (posp chunk))
  (equal (fn2-layout-byte k (+ pos (- chunk 1)) v hi size 1 byte)
         (mv (if (>= (+ pos chunk) size) :done :part) v hi size 1)))
 :hints (("Goal" :in-theory (enable fn2-layout-byte))))
(in-theory (disable fn2-layout-payload-chunk))

'''


def once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f'scan class drift: {old}')
    return text.replace(old,new,1)


def rewrite(source):
    if '(defun fn2-layout-payload-chunk ' in source:
        return source
    parsed=lr.parse(source)
    matches=lr.match('(defun fn2-codec-events ?*body)',parsed.forms,deep=False)
    if len(matches)!=1:
        raise ValueError('expected canonical codec generator')
    node=matches[0].node
    body=source[node.start:node.end]
    old='''           ((mv code v hi size payload)
            (if empty (mv :done 0 0 0 0)
              (,bytefn phase pos v hi size payload byte)))'''
    new='''           (chunk (fn2-layout-payload-chunk (and (not empty) (= payload 1))
                    fuel pos size next end slot gen okind oslot ogen fn2-pool))
           ((mv code v hi size payload)
            (if empty (mv :done 0 0 0 0)
              (,bytefn phase (+ pos (- chunk 1)) v hi size payload byte)))'''
    body=once(body,old,new)
    body=once(body,'(next (if empty next (+ next 1)))',
                   '(next (if empty next (+ next chunk)))')
    body=once(body,'(,scan (- fuel 1) base phase (if (eq code :payload) 0 (+ pos 1))',
                   '(,scan (- fuel chunk) base phase (if (eq code :payload) 0 (+ pos chunk))')
    body=once(body,'(,scan (- fuel 1) base (,nextfn phase)',
                   '(,scan (- fuel chunk) base (,nextfn phase)')
    source=lr.write(source,[(node.start,node.end,body)])
    anchor='(defun fn2-layout-scan '
    return once(source,anchor,SUPPORT+anchor)

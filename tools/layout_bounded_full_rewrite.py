"""Named independent full/model projections over the qualified codec source.

The public generated STEP and its byte-fuel meaning are unchanged.  This is a
source donor pending the actual caller/refinement/guard controls, not activation.
"""
import lisp_rewrite as lr


def one(source, name):
    matches=lr.match(f'(defun {name} ?*body)',lr.parse(source).forms,deep=False)
    if len(matches)!=1:raise ValueError(f'expected {name}')
    return matches[0].node


def once(source, old, new):
    if source.count(old)!=1:raise ValueError('full codec source drift: '+old)
    return source.replace(old,new,1)


def model_error(source):
    """Correct reference error NEXT separately from any full-face behavior."""
    n=one(source,'fn2-layout-decode-run');body=source[n.start:n.end]
    old="((unless (member-eq code '(:ok :more))) (mv code off fn2-fields))"
    new="((unless (member-eq code '(:ok :more))) (mv code n fn2-fields))"
    if new in body:return source
    return lr.write(source,[(n.start,n.end,once(body,old,new))])


FUEL = '''; One extra visit reaches the truncation check after the last available
; byte.  MAX caps malformed tiny-schema prefixes inside a larger page/window.
; Empty fields consume generated scan transitions but consume no input bytes.
(defthm fn2-codec-empty-count-natp
 (natp (fn2-codec-empty-count layout)) :rule-classes :type-prescription)
(defun fn2-layout-full-decode-fuel (layout off end)
 (declare (xargs :guard (fn2-layoutp layout)))
 (+ 1 (min (nfix (- (nfix end) (nfix off))) (nfix (fn2-layout-max-size layout)))
      (fn2-codec-empty-count layout)))
(defthm fn2-layout-full-decode-fuel-positive
 (posp (fn2-layout-full-decode-fuel layout off end))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn2-layout-full-decode-fuel))))
(in-theory (disable fn2-layout-full-decode-fuel))

'''


def full(source):
    """Actual-span full quota and preflight-before-START, one existing scanner."""
    if '(defun fn2-layout-full-decode-fuel ' in source:return source
    # Move the sole existing empty-field counter before its new runtime use;
    # preserve its algorithm and give it the same structural layout guard.
    n=one(source,'fn2-codec-empty-count');empty=source[n.start:n.end]
    empty=once(empty,'(declare (xargs :verify-guards nil))',
        '(declare (xargs :guard (fn2-layoutp layout)\n'
        '                 :guard-hints (("Goal" :use ((:instance fn2-layoutp-head))))))')
    source=lr.write(source,[(n.start,n.end,'')])
    anchor=one(source,'fn2-layout-decode-run').start
    source=lr.write(source,[(anchor,anchor,empty+'\n'+FUEL)])
    n=one(source,'fn2-layout-decode-run');body=source[n.start:n.end]
    body=once(body,'(posp budget) (<= budget 4096) (<= (len layout)',
                   '(posp budget) (or (not resume) (<= budget 4096)) (<= (len layout)')
    source=lr.write(source,[(n.start,n.end,body)])
    old='''  (if (> (fn2-layout-max-size layout) 4096) (mv :budget off fn2-fields)
    (fn2-layout-decode-run layout slot gen off end okind oslot ogen 4096 nil fn2-fields fn2-pool)))'''
    new='''  (fn2-layout-decode-run layout slot gen off end okind oslot ogen
    (fn2-layout-full-decode-fuel layout off end) nil fn2-fields fn2-pool))'''
    source=once(source,old,new)
    n=one(source,'fn2-codec-events');body=source[n.start:n.end]
    old='''      (let ((fn2-fields (,start base fn2-fields)))
        (,step base slot gen off end okind oslot ogen 4096 fn2-fields fn2-pool)))'''
    new='''      (b* ((code (fn2-layout-range-code slot gen off end nil okind oslot ogen fn2-pool))
           ((unless (eq code :ok)) (mv code off fn2-fields))
           ((unless (and (unsigned-byte-p 32 off) (unsigned-byte-p 32 end))) (mv :bounds off fn2-fields))
           (fuel (+ 1 (min (nfix (- end off)) ,max-name) ,(fn2-codec-empty-count layout)))
           (fn2-fields (,start base fn2-fields)))
        (,scan fuel base (fn2-fields-decode-phase base fn2-fields)
          (fn2-fields-decode-pos base fn2-fields) (fn2-fields-decode-acc base fn2-fields)
          (fn2-fields-decode-high base fn2-fields) (fn2-fields-decode-size base fn2-fields)
          (fn2-fields-decode-ref base fn2-fields) (fn2-fields-decode-payload base fn2-fields)
          off slot gen end okind oslot ogen fn2-fields fn2-pool)))'''
    body=once(body,old,new)
    return lr.write(source,[(n.start,n.end,body)])

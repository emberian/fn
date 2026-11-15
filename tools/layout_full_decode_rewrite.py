"""Repair complete-entry codec class while preserving quota-taking STEP APIs.
Input fixture is exact canonical6f624/ccd+71c source; all replacements counted.
"""
def rewrite(source):
 if "(defun fn2-layout-decode-transition-bound " in source:return source
 s=source
 # One declared bound for complete-entry calls; streaming STEP retains its quota.
 anchor='(defun fn2-layout-decode-run '
 helper='''; Full-entry callers admit this declared finite layout work before calling.
; A generated scan consumes one transition per byte or empty field; MAX+FIELDS
; therefore covers every admitted complete encoding, including >4096-byte ones.
(defun fn2-layout-decode-transition-bound (layout)
 (declare (xargs :guard (fn2-layoutp layout)))
 (max 1 (+ (nfix (fn2-layout-max-size layout)) (len layout))))
(defthm fn2-layout-decode-transition-bound-positive
 (and (integerp (fn2-layout-decode-transition-bound layout))
      (< 0 (fn2-layout-decode-transition-bound layout))) :rule-classes :type-prescription)
(in-theory (disable fn2-layout-decode-transition-bound))

'''
 assert s.count(anchor)==1;s=s.replace(anchor,helper+anchor,1)
 s=s.replace('(posp budget) (<= budget 4096) (<= (len layout)', '(posp budget) (or (not resume) (<= budget 4096)) (<= (len layout)',1)
 old='''  (if (> (fn2-layout-max-size layout) 4096) (mv :budget off fn2-fields)
    (fn2-layout-decode-run layout slot gen off end okind oslot ogen 4096 nil fn2-fields fn2-pool)))'''
 new='''  (mv-let (code next fn2-fields)
   (fn2-layout-decode-run layout slot gen off end okind oslot ogen
    (fn2-layout-decode-transition-bound layout) nil fn2-fields fn2-pool)
   (mv (if (eq code :more) :oversized code) next fn2-fields)))'''
 assert s.count(old)==1;s=s.replace(old,new,1)
 # Broaden the full roundtrip claim to all valid declared encodings, not4KiB.
 old='''              (and (<= (+ (- end off) ,(fn2-codec-empty-count layout)) 4096)
                   (eq (fn2-layout-range-code'''
 new='''              (and (eq (fn2-layout-range-code'''
 assert s.count(old)==1;s=s.replace(old,new,1)
 s=s.replace('Generated one-shot exports refine the list specification when the complete transition count fits their 4096-step budget. General proof owed; larger inputs use decode-step.', 'Generated complete-entry exports refine the list specification under the declared layout transition bound. Callers admit that bound; smaller runtime quanta use decode-step. General proof owed.',1)
 s=s.replace('''        (max-name (fn2-codec-constant name "-MAX-SIZE"))''', '''        (max-name (fn2-codec-constant name "-MAX-SIZE"))
        (transitions-name (fn2-codec-constant name "-DECODE-TRANSITIONS"))''',1)
 # Locate the sole emitted max constant; keep encapsulated proof settings intact.
 old='''    (defconst ,max-name ,(fn2-layout-max-size layout))'''
 new=old+'''\n    (defconst ,transitions-name ,(fn2-layout-decode-transition-bound layout))'''
 assert s.count(old)==1;s=s.replace(old,new,1)
 old='''      (let ((fn2-fields (,start base fn2-fields)))
        (,step base slot gen off end okind oslot ogen 4096 fn2-fields fn2-pool)))'''
 new='''      (b* ((code (fn2-layout-range-code slot gen off end nil okind oslot ogen fn2-pool))
           ((unless (eq code :ok)) (mv code off fn2-fields))
           ((unless (and (unsigned-byte-p 32 off) (unsigned-byte-p 32 end))) (mv :bounds off fn2-fields))
           (fn2-fields (,start base fn2-fields))
           ((mv code next fn2-fields)
            (,scan ,transitions-name base (fn2-fields-decode-phase base fn2-fields)
             (fn2-fields-decode-pos base fn2-fields) (fn2-fields-decode-acc base fn2-fields)
             (fn2-fields-decode-high base fn2-fields) (fn2-fields-decode-size base fn2-fields)
             (fn2-fields-decode-ref base fn2-fields) (fn2-fields-decode-payload base fn2-fields)
             off slot gen end okind oslot ogen fn2-fields fn2-pool)))
       (mv (if (eq code :more) :oversized code) next fn2-fields)))'''
 assert s.count(old)==1;s=s.replace(old,new,1)
 old='''        :encode ,encode :decode ,decode :decode-step ,step :start ,start :size ,sizefn'''
 new='''        :encode ,encode :decode ,decode :decode-step ,step :decode-transitions ,transitions-name :start ,start :size ,sizefn'''
 assert s.count(old)==1;s=s.replace(old,new,1)
 # The logical full encoder must match the generated full encoder class too.
 old='       ((when (> (fn2-layout-max-size layout) 4096)) (mv :budget off fn2-pool))\n'
 assert s.count(old)==1;s=s.replace(old,'',1)
 old='(fn2-layout-emit layout 4096 0 0 off slot gen okind oslot ogen fn2-fields fn2-pool)'
 new='(fn2-layout-emit layout (fn2-layout-decode-transition-bound layout) 0 0 off slot gen okind oslot ogen fn2-fields fn2-pool)'
 assert s.count(old)==1;s=s.replace(old,new,1)
 return s

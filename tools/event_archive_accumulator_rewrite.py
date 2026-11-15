"""Bind the actual role3 boot accumulator before its later frame reconstruction."""
import lisp_rewrite as lr


def once(s,old,new):
    if s.count(old)!=1:raise ValueError('accumulator source drift: '+old)
    return s.replace(old,new,1)


def state(s):
    if '(accumulator-slot :u32)' in s:return s
    return once(s,'  (read-armed :bool)',
        '  (accumulator-slot :u32) (accumulator-gen :u60)\n  (read-armed :bool)')


def cursor(s):
    if '(accumulator-slot accumulator)' in s:return s
    s=once(s,'(fn2-event-archive-cold-cursor-begin scratch sgen)',
             '(fn2-event-archive-cold-cursor-begin scratch sgen accumulator agen)')
    anchor='''                    (<= *fn2-commit-unit-bytes* (fn2-pool-cap scratch fn2-pool))'''
    s=once(s,anchor,anchor+'''
                    (unsigned-byte-p 32 accumulator) (unsigned-byte-p 60 agen)
                    (not (equal accumulator scratch)) (not (equal accumulator page))
                    (eq (fn2-pool-workspace-code accumulator agen kind owner gen fn2-pool) :ok)
                    (<= *fn2-commit-unit-bytes* (fn2-pool-cap accumulator fn2-pool))''')
    s=once(s,'(phase *fn2-event-archive-phase-cold-manifest*) (scan 0)',
             '(phase *fn2-event-archive-phase-cold-manifest*) (accumulator-slot accumulator) (accumulator-gen agen) (scan 0)')
    anchor='''            (eq (fn2-pool-workspace-code (fn2-run-loads-scratch c fn2-run-loads) (fn2-run-loads-scratch-gen c fn2-run-loads) kind owner gen fn2-pool) :ok)'''
    return once(s,anchor,anchor+'''
            (not (equal (fn2-event-archive-accumulator-slot 1 fn2-event-archive) (fn2-run-loads-page c fn2-run-loads)))
            (not (equal (fn2-event-archive-accumulator-slot 1 fn2-event-archive) (fn2-run-loads-scratch c fn2-run-loads)))
            (eq (fn2-pool-workspace-code (fn2-event-archive-accumulator-slot 1 fn2-event-archive)
                  (fn2-event-archive-accumulator-gen 1 fn2-event-archive) kind owner gen fn2-pool) :ok)
            (<= *fn2-commit-unit-bytes* (fn2-pool-cap (fn2-event-archive-accumulator-slot 1 fn2-event-archive) fn2-pool))''')


def boot(s):
    if '(accumulator (fn2-machine-pool-slot id fn2-core))' in s:return s
    owner=lr.match('(defun fn2-boot-checkpoint-archive-owner-p ?*body)',lr.parse(s).forms)[0].node
    body=s[owner.start:owner.end]
    body=once(body,'(equal (fn2-machine-phase id fn2-core) phase)',
                   '(equal (fn2-machine-phase id fn2-core) phase) (equal (fn2-machine-root-role id fn2-core) 3)')
    s=lr.write(s,[(owner.start,owner.end,body)])
    s=once(s,'(let ((scratch (fn2-machine-rx-slot id fn2-core)) (sgen (fn2-machine-rx-gen id fn2-core)))',
        '(let ((scratch (fn2-machine-rx-slot id fn2-core)) (sgen (fn2-machine-rx-gen id fn2-core))\n'
        '          (accumulator (fn2-machine-pool-slot id fn2-core)) (agen (fn2-machine-pool-gen id fn2-core)))')
    return once(s,'(fn2-event-archive-cold-cursor-begin scratch sgen fn2-event-archive',
                  '(fn2-event-archive-cold-cursor-begin scratch sgen accumulator agen fn2-event-archive')


def project(kind,source):
    stem=kind.removesuffix('.lisp')
    if stem.endswith('cursor'):return cursor(source)
    if stem.endswith('boot'):return boot(source)
    return source


def fixture(s):
    if '(accumulator-slot accumulator)' in s:return s
    s=once(s,"'((1 . 65536) (1 . 4096))","'((1 . 65536) (2 . 4096))")
    s=once(s,'((mv b scratch sg fn2-pool) (fn2-pool-reserve 1 1 2 3 fn2-pool))',
        '((mv b scratch sg fn2-pool) (fn2-pool-reserve 1 1 2 3 fn2-pool))\n'
        '      ((mv ar accumulator agen fn2-pool) (fn2-pool-reserve 1 1 2 3 fn2-pool))')
    s=once(s,'(header-slot page) (header-gen pg)',
             '(header-slot page) (header-gen pg) (accumulator-slot accumulator) (accumulator-gen agen)')
    s=once(s,'(and (eq a :ok) (eq b :ok)',
             '(and (eq a :ok) (eq b :ok) (eq ar :ok)')
    if '(defun fn2-eamcu-body ' in s:
        anchor='''      ((mv edited fn2-pool) (if (eq fault :leaf)'''
        s=once(s,anchor,'''      (fn2-event-archive (cond
       ((eq fault :accumulator-alias) (fn2-event-archive-set-accumulator-slot 1 scratch fn2-event-archive))
       ((eq fault :accumulator-generation) (fn2-event-archive-set-accumulator-gen 1 (+ 1 agen) fn2-event-archive))
       (t fn2-event-archive)))
'''+anchor)
        s=once(s,"'(:event :generation :owner)","'(:event :generation :owner :accumulator-alias :accumulator-generation)")
        s+='''\n(assert-event (fn2-eamcu-test :accumulator-alias))
(assert-event (fn2-eamcu-test :accumulator-generation))
'''
    elif '(defun fn2-eari-setup ' in s:
        anchor='''       (fn2-checkpoint-bytes (if (eq mode :descriptor)'''
        s=once(s,anchor,'''       (fn2-event-archive (cond
        ((eq mode :accumulator-alias) (fn2-event-archive-set-accumulator-slot 1 (fn2-run-loads-scratch c fn2-run-loads) fn2-event-archive))
        ((eq mode :accumulator-generation) (fn2-event-archive-set-accumulator-gen 1 (+ 1 (fn2-event-archive-accumulator-gen 1 fn2-event-archive)) fn2-event-archive))
        (t fn2-event-archive)))
'''+anchor)
        s+='''\n(assert-event (fn2-eari-test :accumulator-alias))
(assert-event (fn2-eari-test :accumulator-generation))
'''
    return s

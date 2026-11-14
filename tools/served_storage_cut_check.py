"""Bounded source witness for a successful storage fence's unposted return.

Coordinates are executable AST paths and value-flow contracts, not line hashes.
The scheduled Fence stage retains raw results before posting. Execution and
preservation proof qualification remain separate from this source witness.
No OS/FFI correspondence, model execution or ACL2 admission is inferred here.
"""
import copy

import ledger

# An explicit relation, independently checked against the host's enclosing block.
# Missing entries and attribution to normalizing/posting transitions are errors.
FENCE_CUTS = {
    ('fn2-device-worker', 'device-syscall'): 'before-physical',
    ('fn2-device-worker', 'device-syscall-return'): 'physical-returned-unposted',
    ('fn2-n-storage-completions', 'device-return'): 'physical-returned-unposted',
}


# Fixed enclosing control positions: moving a contract into a dead branch or
# leaving a disconnected copy cannot satisfy the witness. Paths alone carry no
# evidence; each must also contain its exact argument/effect contract below.
CONTEXT_PATHS = {'physical call between callbacks, before completion publication': [3, 1, 1],
 'actual action-to-device-kind dispatch': [3],
 'fence branch uses the device fd': [3, 1, 1, 1, 2, 2, 4],
 'raw return and errno retained before return callback': [3, 2],
 'same incarnation and raw return recorded before death cut and terminal normalization': [3,
                                                                                          2,
                                                                                          3,
                                                                                          3],
 'physical dispatcher threads actual effect and raw result back to completion': [4, 3, 2],
 'fence effect returns storage before any terminal post': [4, 4],
 'physical failure includes sticky device death': [4, 2, 3, 1, 0],
 'successful physical result returns effected storage': [4, 2, 3, 2],
 'successful nonlying fence commits its captured snapshot': [4, 2, 3, 1, 1, 1],
 'captured bytes become durable in commit traversal': [4, 3, 1, 1, 1, 2, 2, 1, 0, 1],
 'selected noncancelled physical result binding': [4, 3, 2, 4, 1, 1, 1],
 'normalization/post consumes the same physical return': [4, 3, 2, 4, 1, 1, 3],
 'atomic comparison helper physical-to-terminal suffix': [4, 3, 2, 4, 1],
 'storage fence cannot enter send borrow-release phases': [4, 3, 1, 7],
 'release-only active phases': [4, 3, 1, 5],
 'early release requires send release': [4, 1, 4],
 'actual scheduled caller selects split completion': [4, 2],
 'scheduled Fence returns with retained raw packet and no terminal post': [4, 3],
 'later scheduled step consumes retained raw return without physical reissue': [4, 2],
 'staged path uses the shared physical effect': [4, 3, 1, 5],
 'packet retains actual raw result and original fault coordinate': [4, 3, 1, 7],
 'every shared Fence stage retains the same raw packet': [4, 3, 1, 8],
 'returned stage excludes crash-flight write replay': [4, 3, 1, 9],
 'all raw result and scheduling scalars stored without normalization': [4],
 'same incarnation and retained raw scalars reconstructed for post': [4],
 'Fence post cannot substitute a different retained physical result': [4, 1, 1, 3],
 'retained raw result reaches shared terminal normalization exactly': [4, 3]}


def ast(source):
    return ledger.read_forms(source)[0]


def locations(form, target, path=()):
    """Paths retain enclosing control/argument positions, unlike a call count."""
    if form == target:
        yield list(path)
    if isinstance(form, list) and ledger.head(form) not in ('quote', 'declare'):
        for i, child in enumerate(form):
            yield from locations(child, target, path + (i,))


def check(defs, mappings=None):
    mappings = FENCE_CUTS if mappings is None else mappings
    findings, evidence = [], []

    def require(name, source, description):
        target = ast(source)
        paths = list(locations(defs.get(name, []), target))
        if paths != [CONTEXT_PATHS[description]]:
            findings.append(f'fence cut witness {name}: {description} missing, moved or duplicated')
        else:
            evidence.append({'function': name, 'ast_path': paths[0],
                             'contract': source, 'role': description})
        return target

    # Entire worker iteration body: the return boundary is outside PERFORM,
    # and before publishing the job into DONE. Both callbacks have the same
    # actual device argument. A new branch or extra call invalidates the slice.
    worker = require('fn2-device-worker', '''
      (let ((job
              (sb-thread:with-mutex ((fn2-device-lock device))
                (loop while (and (zerop (fn2-device-pending device))
                                 (not (fn2-device-stopping device)))
                      do (sb-thread:condition-wait (fn2-device-available device) (fn2-device-lock device)))
                (when (fn2-device-stopping device) (return-from fn2-device-worker nil))
                (let* ((q (fn2-device-queue device)) (i (fn2-device-head device)) (job (aref q i)))
                  (setf (aref q i) nil (fn2-device-head device) (mod (1+ i) (length q)))
                  (decf (fn2-device-pending device)) job))))
        (when (fn2-device-boundary device)
          (funcall (fn2-device-boundary device) "device-syscall"))
        (fn2-device-perform device job)
        (when (fn2-device-boundary device)
          (funcall (fn2-device-boundary device) "device-syscall-return"))
        (sb-thread:with-mutex ((fn2-device-lock device))
          (when (fn2-device-stopping device) (return-from fn2-device-worker nil))
          (let ((q (fn2-device-done device)))
            (assert (< (fn2-device-completed device) (length q)))
            (setf (aref q (fn2-device-dtail device)) job
                  (fn2-device-dtail device) (mod (1+ (fn2-device-dtail device)) (length q)))
            (incf (fn2-device-completed device)))
          (funcall (fn2-device-wake device))))''', 'physical call between callbacks, before completion publication')
    require('fn2-n-storage-kind', '''
      (cond ((= kind *fn2-action-read*) :read)
            ((= kind *fn2-action-write*) :write)
            ((= kind *fn2-action-fence*) :fence))''', 'actual action-to-device-kind dispatch')
    require('fn2-device-perform', '(:fence (fn2-device-fence (fn2-device-fd device)))',
            'fence branch uses the device fd')
    require('fn2-device-perform', '''
      (setf (fn2-device-job-result job) n
            (fn2-device-job-errno job) (if (minusp n) (fn2-native-errno) 0))''',
            'raw return and errno retained before return callback')
    require('fn2-n-storage-completions', '''
      (let ((op (aref (fn2-nhost-ops host) (fn2-device-job-slot job))))
        (assert (= (fn2-nop-gen op) (fn2-device-job-gen job)))
        (multiple-value-bind (code count)
            (fn2-device-io-observation (fn2-device-job-result job) (fn2-device-job-errno job))
          (when (eq (fn2-device-job-kind job) :fence)
            (fn2-n-record host
              (list :physical-return
                (list (fn2-device-job-slot job) (fn2-device-job-gen job)
                  (fn2-nop-kind op) (fn2-terminal-event (fn2-nop-kind op)) (fn2-nop-len op)
                  code count 0 0 0 *fn2-fault-none*)
                (fn2-device-job-result job) (fn2-device-job-errno job))))
          (fn2-n-boundary host "device-return")
          (fn2-n-complete host (fn2-device-job-slot job) code count 0 nil
            (and (eq (fn2-device-job-kind job) :read)
                 (fn2-n-octets host (fn2-device-job-address job) count))))
        (decf (fn2-nhost-storage-pending host)))''',
        'same incarnation and raw return recorded before death cut and terminal normalization')

    # Derive the observed phase at each callback by executing this checked
    # straight-line block's effect projection. This does not execute foreign I/O.
    observed = {}
    phase = 'before-physical'
    for form in worker[2:]:
        if form == ast('(fn2-device-perform device job)'):
            phase = 'physical-returned-unposted'
        elif ledger.head(form) == 'when':
            callback = form[2] if len(form) == 3 else []
            if ledger.head(callback) == 'funcall':
                observed[('fn2-device-worker', str(callback[2]))] = phase
    observed[('fn2-n-storage-completions', 'device-return')] = 'physical-returned-unposted'
    for site in sorted(observed.keys() | mappings.keys()):
        if mappings.get(site) != observed.get(site):
            findings.append(f'fence cut relation {site}: expected {observed.get(site)!r}, got {mappings.get(site)!r}')

    # The model counterpart is after the real fence effect, before normalization
    # and any FN2-SIM-POST. No completed terminal may stand in for this prefix.
    require('fn2-sim-physical', '''
      (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim))
                  (fn2-sim-storage (fn2-sim-disk fn2-sim)))
        (code count aux fn2-core fn2-sim-network fn2-sim-storage fn2-own)
        (fn2-sim-physical-act kind cap nonce rslot rgen off len n okind oslot ogen slot gen offset stamp fua fault word lying
                              fn2-core fn2-sim-network fn2-sim-storage fn2-own)
        (let ((fn2-sim
               (if (fn2-sim-physical-landed-p kind fault code count len offset disk-bytes disk-alive dirty-fence lying)
                   (fn2-sim-land fault fn2-sim) fn2-sim)))
          (mv code count aux fn2-core fn2-sim fn2-own)))''',
        'physical dispatcher threads actual effect and raw result back to completion')
    require('fn2-sim-physical-act', '''
      ((equal kind *fn2-action-fence*)
        (mv-let (code fn2-sim-storage)
          (fn2-storage-fence-complete slot (equal fault *fn2-fault-flush-io*) lying fn2-sim-storage)
          (mv code 0 0 fn2-core fn2-sim-network fn2-sim-storage fn2-own)))''',
        'fence effect returns storage before any terminal post')
    require('fn2-storage-fence-complete', '(failed (or fail (equal (fn2-storage-dead fn2-sim-storage) 1)))',
            'physical failure includes sticky device death')
    require('fn2-storage-fence-complete', '(mv (if failed :io :ok) fn2-sim-storage)',
            'successful physical result returns effected storage')
    require('fn2-storage-fence-complete', '''
      (if (or failed lie) fn2-sim-storage
        (fn2-storage-fence-bytes 0 (* slot (fn2-sim-storage-rows fn2-sim-storage)) t fn2-sim-storage))''',
        'successful nonlying fence commits its captured snapshot')
    require('fn2-storage-fence-bytes',
            '(fn2-sim-storage-set-durable i (fn2-storage-snapshoti j fn2-sim-storage) fn2-sim-storage)',
            'captured bytes become durable in commit traversal')
    require('fn2-sim-complete', '''
      ((mv code physical-count aux fn2-core fn2-sim fn2-own)
        (if (= was-cancelled 1)
            (mv :cancelled 0 0 fn2-core fn2-sim fn2-own)
          (fn2-sim-physical slot fault word fn2-core fn2-sim fn2-own)))''',
        'selected noncancelled physical result binding')
    require('fn2-sim-complete', '''
      ((mv found fn2-core fn2-sim fn2-own)
        (fn2-sim-complete-result slot gen kind event len code physical-count aux
          fault word now release fn2-core fn2-sim fn2-own))''',
        'normalization/post consumes the same physical return')
    # Atomic comparison helper remains unchanged. It is no longer the actual
    # scheduled Fence path in this domain; the stage below is the real subject.
    require('fn2-sim-complete', '''
      (b* (((mv & fn2-core fn2-sim fn2-own)
              (fn2-sim-inject slot fault fn2-core fn2-sim fn2-own))
           ((mv code physical-count aux fn2-core fn2-sim fn2-own)
              (if (= was-cancelled 1)
                  (mv :cancelled 0 0 fn2-core fn2-sim fn2-own)
                (fn2-sim-physical slot fault word fn2-core fn2-sim fn2-own)))
           ((when (and (eq code :would-block) (equal physical-count 0)))
              (let ((fn2-sim (fn2-sim-set-due slot
                              (min *fn2-u60-max* (+ 100 now)) fn2-sim)))
                (mv t fn2-core fn2-sim fn2-own)))
           ((mv found fn2-core fn2-sim fn2-own)
              (fn2-sim-complete-result slot gen kind event len code physical-count aux
                fault word now release fn2-core fn2-sim fn2-own)))
        (mv found fn2-core fn2-sim fn2-own))''',
        'atomic comparison helper physical-to-terminal suffix')
    require('fn2-sim-complete', '''
      (release (and (equal kind *fn2-action-send*) (= (fn2-sim-may-release slot fn2-sim) 1)))''',
        'storage fence cannot enter send borrow-release phases')
    require('fn2-sim-terminal-post', '''
      (fn2-sim (fn2-sim-set-active slot (cond (early 3) (release 2) (t 0)) fn2-sim))''',
        'release-only active phases')
    require('fn2-sim-complete-result',
            '(early (and release (equal fault *fn2-fault-release-order*)))',
            'early release requires send release')

    require('fn2-sim-advance-flight', """
      (if (and (not automatic) (equal (fn2-sim-active slot fn2-sim) 1)
               (equal (fn2-sim-kind slot fn2-sim) *fn2-action-accept*))
          (fn2-sim-echo-accept slot fault word allow-accept fn2-core fn2-sim fn2-own)
        (fn2-sim-step-completion slot fault word fn2-core fn2-sim fn2-own))""",
        'actual scheduled caller selects split completion')
    require('fn2-sim-step-completion', """
      ((and (fn2-sim-native-storagep slot fn2-sim)
            (= (fn2-sim-kind slot fn2-sim) *fn2-action-fence*)
            (fn2-sim-native-faultp fault))
       (b* (((mv status packet fn2-core fn2-sim fn2-own)
             (fn2-sim-native-stage slot fault word fn2-core fn2-sim fn2-own))
            (- packet))
         (mv (if (member-eq status '(:returned :waiting)) t nil) fn2-core fn2-sim fn2-own)))""",
        'scheduled Fence returns with retained raw packet and no terminal post')
    require('fn2-sim-step-completion', """
      ((= (fn2-sim-active slot fn2-sim) *fn2-sim-native-returned*)
       (if (= (fn2-sim-kind slot fn2-sim) *fn2-action-fence*)
           (fn2-sim-native-post (fn2-sim-saved-return slot fn2-sim) fn2-core fn2-sim fn2-own)
         (mv nil fn2-core fn2-sim fn2-own)))""",
        'later scheduled step consumes retained raw return without physical reissue')
    require('fn2-sim-native-stage', """
      ((mv code count aux fn2-core fn2-sim fn2-own)
        (fn2-sim-physical slot fault word fn2-core fn2-sim fn2-own))""",
        'staged path uses the shared physical effect')
    require('fn2-sim-native-stage',
            '(packet (list slot gen kind event len code count aux word now fault))',
            'packet retains actual raw result and original fault coordinate')
    require('fn2-sim-native-stage',
            '(fn2-sim (if (equal kind *fn2-action-fence*) (fn2-sim-save-return packet fn2-sim) fn2-sim))',
            'every shared Fence stage retains the same raw packet')
    require('fn2-sim-native-stage',
            '(fn2-sim (fn2-sim-set-active slot *fn2-sim-native-returned* fn2-sim))',
            'returned stage excludes crash-flight write replay')
    require('fn2-sim-save-return', """
      (fn2-sim-put (nth 0 packet)
        (return-code (fn2-sim-return-code-keyword->code (nth 5 packet)))
        (return-count (nth 6 packet)) (return-aux (nth 7 packet))
        (return-word (nth 8 packet)) (return-time (nth 9 packet)) (return-fault (nth 10 packet)))""",
        'all raw result and scheduling scalars stored without normalization')
    require('fn2-sim-saved-return', """
      (list slot (fn2-sim-gen slot fn2-sim) (fn2-sim-kind slot fn2-sim)
        (fn2-terminal-event (fn2-sim-kind slot fn2-sim)) (fn2-sim-range-len slot fn2-sim)
        (fn2-sim-return-code-code->keyword (fn2-sim-return-code slot fn2-sim))
        (fn2-sim-return-count slot fn2-sim) (fn2-sim-return-aux slot fn2-sim)
        (fn2-sim-return-word slot fn2-sim) (fn2-sim-return-time slot fn2-sim)
        (fn2-sim-return-fault slot fn2-sim))""",
        'same incarnation and retained raw scalars reconstructed for post')
    require('fn2-sim-native-post', """
      (or (not (equal (nth 2 packet) *fn2-action-fence*))
          (equal packet (fn2-sim-saved-return (nth 0 packet) fn2-sim)))""",
        'Fence post cannot substitute a different retained physical result')
    require('fn2-sim-native-post', """
      (let ((fn2-sim (fn2-sim-set-active (nth 0 packet) 1 fn2-sim)))
       (fn2-sim-complete-result (nth 0 packet) (nth 1 packet) (nth 2 packet)
         (nth 3 packet) (nth 4 packet) (nth 5 packet) (nth 6 packet) (nth 7 packet)
         (nth 10 packet) (nth 8 packet) (nth 9 packet) nil fn2-core fn2-sim fn2-own))""",
        'retained raw result reaches shared terminal normalization exactly')

    # The outer check also validates crash ordering and exact shared terminal
    # ABI. Do not invent an outer crash point here merely because these internal
    # functions can be called separately in a fixture.
    return {'family': 'successful-nonlying-storage-fence-return',
            'source_ok': not findings, 'findings': findings,
            'domain': ['submitted fresh fence with active=1 and captured snapshot', 'matching slot/generation',
                       'not cancelled', 'physical return :ok', 'fault none; lying nil'],
            'cuts': [{'host_function': site[0], 'label': site[1], 'phase': phase,
                      'model_function': 'fn2-sim-step-completion',
                      'model_prefix': 'before fn2-sim-physical' if phase == 'before-physical'
                                      else 'after fn2-sim-native-stage, before fn2-sim-native-post',
                      'terminal_posted': False} for site, phase in sorted(observed.items())],
            'evidence': copy.deepcopy(evidence),
            'model_composition': 'scheduled-source-present; execution and preservation qualification pending',
            'excluded_branches': [{'branch': 'fn2-sim-complete active=2 or active=3',
                                   'status': 'unreachable-in-composition for fresh fence: release and early require Send'}],
            'mapping_complete': False,
            'remaining': ['qualify scheduled physical-return/post split and raw packet roundtrip',
                          'prove initialized operation-incarnation/effect relation and crash preservation',
                          'bind native fence/FFI/OS contract and model snapshot coverage',
                          'read/write/error/cancel/concurrent-worker cut families',
                          'physical-return trace/replay correspondence']}

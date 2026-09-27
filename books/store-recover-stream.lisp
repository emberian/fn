; fn: THE CHUNKED FULL REPLAY (lane recover-memory, 2026-09-27; PKT-823; D27).
;
; The full replay used to hand ACL2 the whole history at once: the host
; converted every record to an octet list (sixteen bytes per octet), ACL2
; decoded every one into a wire event (another list copy of each payload),
; and only then interned the events into the arena.  On the 10,064-record
; 32 KiB fixture that was 5.1 GB of octet lists plus 5.1 GB of decoded
; events live together (planning/evidence/recover-memory-2026-09-27.md).
;
; The open now takes the history in chunks: `fn-srs-step' decodes one chunk
; of record octets and interns it into the arena (`fn-srs-intern-step'),
; accumulating the rows newest first.  The host makes the step's two calls
; once per chunk (host/native/io.lisp fnn-bridge-recover:
; fn-store-decode-records, which is fn-srs-decode, then the guard-verified
; fn-srs-intern-step with the live arena), then opens over `fn-srs-rows'
; (host/store-node-host.lisp fn-store-sn-recover-rows).  A chunk ends where `fn-srs-chunk-fullp' says (a work
; quantum: at least one record, whatever its size; never a bound on data).
;
; KEYSTONE `fn-srs-steps-are-one-step-of-the-concatenation': folding the
; step over ANY split of the history into chunks answers what one step over
; the whole history answers: :bad exactly when it is :bad, and otherwise the
; same rows and the same arena.  One step over the whole history is the
; intern of the decoded history (fn-srs-one-step-is-the-intern-of-the-decode),
; which is what the open computed before the chunking, so the chunking the
; host picks cannot change the opened Store.
(in-package "ACL2")
(include-book "store-intern")
(include-book "records-concrete")

; -----------------------------------------------------------------------------
; 1. The decode of a list of record octets (the host's fn-store-decode-records,
; now this function): every record decodes exactly to a wire event, else :bad.

(defun fn-srs-decode (octet-records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp octet-records)
      (let ((decoded (fn-store-event-decode-exact (car octet-records))))
        (if (and (consp decoded) (equal (car decoded) :ok)
                 (consp (cdr decoded)) (fn-rcon-wire-event-p (car (cdr decoded))))
            (let ((rest (fn-srs-decode (cdr octet-records))))
              (if (equal rest :bad) :bad (cons (car (cdr decoded)) rest)))
          :bad))
    (if (null octet-records) nil :bad)))

; The codec and the recognizer stay closed below: every fact here is about
; the list walk, not about what one record decodes to.
(local (in-theory (disable fn-store-event-decode-exact fn-rcon-wire-event-p)))

(defthm fn-srs-decode-true-listp
  (or (true-listp (fn-srs-decode x)) (equal (fn-srs-decode x) :bad))
  :rule-classes :type-prescription)

(defthm fn-srs-decode-of-append
  (implies (true-listp a)
           (equal (fn-srs-decode (append a b))
                  (if (or (equal (fn-srs-decode a) :bad)
                          (equal (fn-srs-decode b) :bad))
                      :bad
                    (append (fn-srs-decode a) (fn-srs-decode b)))))
  :hints (("Goal" :induct (fn-srs-decode a))))

; -----------------------------------------------------------------------------
; 2. The intern of a concatenation is the intern of its parts, the arena
; threaded (books/store-intern.lisp fn-intern-events).

(local
 (defthm fn-srs-append-not-bad
   (implies (not (equal y :bad)) (not (equal (append x y) :bad)))))

(defthm fn-srs-intern-events-of-append
  (let ((ra (mv-nth 0 (fn-intern-events a keyring generation fn-arena)))
        (arena1 (mv-nth 1 (fn-intern-events a keyring generation fn-arena))))
    (and (equal (mv-nth 1 (fn-intern-events (append a b) keyring generation fn-arena))
                (if (eq ra :bad)
                    arena1
                  (mv-nth 1 (fn-intern-events b keyring generation arena1))))
         (equal (mv-nth 0 (fn-intern-events (append a b) keyring generation fn-arena))
                (if (eq ra :bad)
                    :bad
                  (let ((rb (mv-nth 0 (fn-intern-events b keyring generation arena1))))
                    (if (eq rb :bad) :bad (append ra rb)))))))
  :hints (("Goal" :induct (fn-intern-events a keyring generation fn-arena)
           :expand ((binary-append a b)
                    (fn-intern-events (cons (car a) (append (cdr a) b))
                                      keyring generation fn-arena))
           :in-theory (union-theories '(fn-intern-events binary-append car-cons cdr-cons
                                        mv-nth zp default-car default-cdr
                                        (:type-prescription fn-intern-event)
                                        (:type-prescription fn-intern-events)
                                        (:type-prescription binary-append)
                                        fn-srs-append-not-bad)
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 3. The step, its fold, and the chunk quantum.

(defthm fn-srs-intern-events-true-listp
  (implies (not (eq (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad))
           (true-listp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-intern-events) (fn-intern-event)))))

; ACC is the rows so far, newest first, or :bad once a chunk was refused.
; The intern is the open's: keyring NIL, generation 0 (store-intern's note).
; The host calls this directly with the live arena (guard-verified, so no
; :program entry updates the arena: flip-L6-2's invariant-risk finding).
(defun fn-srs-intern-step (acc ws fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :guard-hints (("Goal" :use ((:instance fn-srs-intern-events-true-listp
                                                 (keyring nil) (generation 0)))
                                 :in-theory (disable fn-intern-events
                                                     fn-srs-intern-events-true-listp)))))
  (if (or (eq acc :bad) (eq ws :bad))
      (mv :bad fn-arena)
    (mv-let (rows fn-arena)
      (fn-intern-events ws nil 0 fn-arena)
      (if (eq rows :bad)
          (mv :bad fn-arena)
        (mv (revappend rows acc) fn-arena)))))

; One chunk of record octets: its decode, then the intern step.  The host
; makes exactly these two calls per chunk (host/native/io.lisp
; fnn-bridge-recover: fn-store-decode-records, which is fn-srs-decode, then
; fn-srs-intern-step).
(defun fn-srs-step (acc octet-records fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-srs-intern-step acc (fn-srs-decode octet-records) fn-arena))

; The rows oldest first, what the open (fn-store-sn-recover-rows) takes.
(defun fn-srs-rows (acc)
  (declare (xargs :guard t))
  (reverse (true-list-fix acc)))

(defun fn-srs-steps (chunks acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (atom chunks)
      (mv acc fn-arena)
    (mv-let (acc fn-arena)
      (fn-srs-step acc (car chunks) fn-arena)
      (fn-srs-steps (cdr chunks) acc fn-arena))))

(defun fn-srs-concat (chunks)
  (declare (xargs :guard t))
  (if (atom chunks)
      nil
    (append (true-list-fix (car chunks)) (fn-srs-concat (cdr chunks)))))

(defun fn-srs-chunksp (chunks)
  (declare (xargs :guard t))
  (if (atom chunks)
      t
    (and (true-listp (car chunks)) (fn-srs-chunksp (cdr chunks)))))

; The quantum: a chunk closes once it holds this many record octets.  A
; single record larger than the quantum is a chunk by itself; nothing is
; refused or split for its size.
(defconst *fn-srs-chunk-octets* 1048576)

(defun fn-srs-chunk-fullp (octets)
  (declare (xargs :guard t))
  (and (natp octets) (<= *fn-srs-chunk-octets* octets)))

;; -----------------------------------------------------------------------------
; 4. The keystone.

; X answers as Y does: :bad exactly when Y is, and otherwise equal.
(defun fn-srs-same (x y)
  (declare (xargs :guard t))
  (if (eq (mv-nth 0 y) :bad)
      (eq (mv-nth 0 x) :bad)
    (equal x y)))

(local
 (defthm fn-srs-same-transitive
   (implies (and (fn-srs-same x y) (fn-srs-same y z))
            (fn-srs-same x z))))

(local
 (defthm fn-srs-step-of-bad
   (equal (fn-srs-step :bad x fn-arena) (mv :bad fn-arena))))

(local
 (defthm fn-srs-steps-of-bad
   (equal (fn-srs-steps chunks :bad fn-arena) (mv :bad fn-arena))))

(local
 (defthm fn-srs-revappend-append
   (equal (revappend (append a b) acc) (revappend b (revappend a acc)))))

(local
 (defthm fn-srs-revappend-not-bad
   (implies (not (equal acc :bad)) (not (equal (revappend x acc) :bad)))))

(local
 (defthm fn-srs-two-steps
   (implies (true-listp a)
            (fn-srs-same (mv-let (acc1 arena1) (fn-srs-step acc a fn-arena)
                           (fn-srs-step acc1 b arena1))
                         (fn-srs-step acc (append a b) fn-arena)))
   :hints (("Goal" :in-theory (disable fn-intern-events fn-srs-decode revappend)))))

(local
 (defthm fn-srs-steps-same
   (implies (fn-srs-chunksp chunks)
            (fn-srs-same (fn-srs-steps chunks acc fn-arena)
                         (fn-srs-step acc (fn-srs-concat chunks) fn-arena)))
   :hints (("Goal" :induct (fn-srs-steps chunks acc fn-arena)
            :in-theory (disable fn-srs-step fn-srs-same))
           ("Subgoal *1/1" :in-theory (enable fn-srs-step fn-srs-same))
           ("Subgoal *1/2" :use ((:instance fn-srs-two-steps (a (car chunks))
                                            (b (fn-srs-concat (cdr chunks))))
                                 (:instance fn-srs-same-transitive
                                  (x (fn-srs-steps (cdr chunks)
                                                   (mv-nth 0 (fn-srs-step acc (car chunks) fn-arena))
                                                   (mv-nth 1 (fn-srs-step acc (car chunks) fn-arena))))
                                  (y (fn-srs-step (mv-nth 0 (fn-srs-step acc (car chunks) fn-arena))
                                                  (fn-srs-concat (cdr chunks))
                                                  (mv-nth 1 (fn-srs-step acc (car chunks) fn-arena))))
                                  (z (fn-srs-step acc (fn-srs-concat chunks) fn-arena))))))))

; KEYSTONE.
(defthm fn-srs-steps-are-one-step-of-the-concatenation
  (implies (fn-srs-chunksp chunks)
           (let ((steps (fn-srs-steps chunks acc fn-arena))
                 (one (fn-srs-step acc (fn-srs-concat chunks) fn-arena)))
             (and (iff (eq (mv-nth 0 steps) :bad) (eq (mv-nth 0 one) :bad))
                  (implies (not (eq (mv-nth 0 one) :bad))
                           (equal steps one)))))
  :hints (("Goal" :use fn-srs-steps-same
           :in-theory (union-theories '(fn-srs-same iff)
                                      (theory 'minimal-theory)))))

; The one step from no rows is the open's intern of the decoded history, the
; rows oldest first (fn-srs-rows, what fn-store-sn-recover-rows opens over):
; the value the one-shot open computed before the chunking.
(defthm fn-srs-one-step-is-the-intern-of-the-decode
  (let ((ws (fn-srs-decode octet-records)))
    (implies (not (eq (mv-nth 0 (fn-srs-step nil octet-records fn-arena)) :bad))
             (and (not (eq ws :bad))
                  (equal (fn-srs-rows (mv-nth 0 (fn-srs-step nil octet-records fn-arena)))
                         (mv-nth 0 (fn-intern-events ws nil 0 fn-arena)))
                  (equal (mv-nth 1 (fn-srs-step nil octet-records fn-arena))
                         (mv-nth 1 (fn-intern-events ws nil 0 fn-arena))))))
  :hints (("Goal" :use ((:instance fn-srs-intern-events-true-listp
                                   (ws (fn-srs-decode octet-records))
                                   (keyring nil) (generation 0)))
           :in-theory (disable fn-intern-events fn-srs-decode
                               fn-srs-intern-events-true-listp))))

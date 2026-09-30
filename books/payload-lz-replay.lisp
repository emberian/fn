; fn: the replay and the commit with compressed records (lane
; compression-extents, PRF-326; split from books/payload-lz-record.lisp to keep
; each book under 10 s).  The replay's intern step seals a frame whose block
; decodes to the record's payload as a COMPRESSED extent (KEYSTONE
; fn-lzr-intern-step-refines: under the faithful places it is the resident
; step); the commit re-points a fenced handle at its frame's block (KEYSTONE
; fn-lzr-commit-reseats-keep-the-arena).  The frame, the extent and its read
; are books/payload-lz-record.lisp.

(in-package "ACL2")
(include-book "payload-lz-record")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-arn-extent-guardp)
                          (:definition fn-arn-lz-guardp)
                          (:rewrite fn-stxa-is-no-other-wire-event)
                          (:rewrite fn-intern-event-arena))))

; -----------------------------------------------------------------------------
; 8. The replay's intern with compressed extents.
;
; The host expands each record of a chunk (`fn-lzr-expand-chunk'), decodes
; the expansions as today, and interns each decoded event with the octets
; the log holds (Z) and its place: a frame whose C decodes to the record's
; payload is sealed as a COMPRESSED extent (no payload octets on the heap);
; any other record goes to the plain extent intern
; (books/payload-extent.lisp fn-arx-intern-event).

(defun fn-lzr-expand-chunk (dicts zs)
  (declare (xargs :guard (fn-lzr-dictsp dicts)))
  (if (atom zs)
      nil
    (let ((x (if (fn-cbor-octet-listp (car zs)) (fn-lzr-expand dicts (car zs)) (list :ok (car zs)))))
      (if (eq (car x) :ok)
          (let ((rest (fn-lzr-expand-chunk dicts (cdr zs))))
            (if (eq rest :bad) :bad (cons (cadr x) rest)))
        :bad))))

(defun fn-lzr-cat-intern-lz (w x dict keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-record-p w) (fn-prin-keyringp keyring) (natp generation)
                              (fn-lzr-extentp x) (fn-cbor-octet-listp dict))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let* ((bytes (fn-record-payload w))
         (h (fn-arena-count fn-arena))
         (fn-arena (fn-arena-seal-lz-extent (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)
                                            (nth 5 x) (nth 6 x) dict fn-arena)))
    (mv (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                      (fn-record-generation w) (fn-record-msgid w) h
                      (fn-record-groups w) (fn-record-obligation-id w)
                      (fn-record-content-subject w) (fn-record-release-evidence w)
                      (fn-record-charge w) (fn-record-stamp w)
                      (fn-held-facts-of bytes)
                      (fn-held-context-of bytes keyring generation)
                      nil nil (fn-row-binding w))
        fn-arena)))

(defun fn-lzr-intern-event (w z position file dicts keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp file) (fn-lzr-dictsp dicts)
                              (fn-prin-keyringp keyring) (natp generation))
                  :guard-hints (("Goal" :in-theory (disable fn-record-p fn-arx-intern-event
                                                            fn-lzr-cat-intern-lz)))))
  (let ((x (and (fn-record-p w) (fn-cbor-octet-listp z) (true-listp position)
                (fn-lzr-dictsp dicts)
                (fn-lzr-extent-of file position z (fn-record-payload w) dicts))))
    (if x
        (fn-lzr-cat-intern-lz w x (cdr (assoc-equal (nth 7 x) dicts)) keyring generation fn-arena)
      (fn-arx-intern-event w z position file keyring generation fn-arena))))

; Executes by a loop (lane depth-debt, PRF-919): the recursion took one
; control-stack frame per element of data with no fixed cap.  The :logic is
; the recursion, unchanged; the :exec is the loop, equal by the lemma below.
(defun fn-lzr-intern-events-loop (ws zs ps dicts keyring generation acc fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-lzr-dictsp dicts) (fn-prin-keyringp keyring) (natp generation))
                  :guard-hints (("Goal" :in-theory (disable fn-lzr-intern-event)))))
  (if (atom ws)
      (mv (fn-ag-rev-onto acc nil) fn-arena)
    (let* ((z (and (consp zs) (car zs)))
           (p (and (consp ps) (consp (car ps)) (car ps)))
           (file (nfix (and (consp p) (car p))))
           (position (and (consp p) (cdr p))))
      (mv-let (row fn-arena)
        (fn-lzr-intern-event (car ws) z position file dicts keyring generation fn-arena)
        (if (eq row :bad)
            (mv :bad fn-arena)
          (fn-lzr-intern-events-loop (cdr ws) (and (consp zs) (cdr zs)) (and (consp ps) (cdr ps))
                                     dicts keyring generation (cons row acc) fn-arena))))))

(defun fn-lzr-intern-events (ws zs ps dicts keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-lzr-dictsp dicts) (fn-prin-keyringp keyring) (natp generation))
                  :verify-guards nil))
  (mbe :logic
  (if (atom ws)
      (mv nil fn-arena)
    (let* ((z (and (consp zs) (car zs)))
           (p (and (consp ps) (consp (car ps)) (car ps)))
           (file (nfix (and (consp p) (car p))))
           (position (and (consp p) (cdr p))))
      (mv-let (row fn-arena)
        (fn-lzr-intern-event (car ws) z position file dicts keyring generation fn-arena)
        (if (eq row :bad)
            (mv :bad fn-arena)
          (mv-let (rest fn-arena)
            (fn-lzr-intern-events (cdr ws) (and (consp zs) (cdr zs)) (and (consp ps) (cdr ps))
                                  dicts keyring generation fn-arena)
            (if (eq rest :bad)
                (mv :bad fn-arena)
              (mv (cons row rest) fn-arena)))))))
  :exec (fn-lzr-intern-events-loop ws zs ps dicts keyring generation nil fn-arena)))

(defthm fn-lzr-intern-events-loop-is-rev-onto
  (equal (fn-lzr-intern-events-loop ws zs ps dicts keyring generation acc fn-arena)
         (mv-let (r a) (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)
           (mv (if (eq r :bad) :bad (fn-ag-rev-onto acc r)) a)))
  :hints (("Goal" :induct (fn-lzr-intern-events-loop ws zs ps dicts keyring generation acc
                                                     fn-arena)
                  :do-not '(generalize fertilize eliminate-destructors)
                  :in-theory (disable fn-lzr-intern-event nfix))))

(verify-guards fn-lzr-intern-events
  :hints (("Goal" :in-theory (disable fn-lzr-intern-event))))

(defthm fn-lzr-intern-events-true-listp
  (or (true-listp (mv-nth 0 (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)))
      (equal (mv-nth 0 (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)) :bad))
  :rule-classes nil
  :hints (("Goal" :induct (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)
           :in-theory (disable fn-lzr-intern-event))))

; The chunk step the host calls (host/native/io.lisp, the log stream's
; flush): WS the decoded expansions, ZS the octets the log holds, PS their
; places, DICTS the store's dictionaries.
(defun fn-lzr-intern-step (acc ws zs ps dicts fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-lzr-dictsp dicts)
                  :guard-hints (("Goal" :use ((:instance fn-lzr-intern-events-true-listp
                                                 (keyring nil) (generation 0)))
                                 :in-theory (disable fn-lzr-intern-events)))))
  (if (or (eq acc :bad) (eq ws :bad))
      (mv :bad fn-arena)
    (mv-let (rows fn-arena)
      (fn-lzr-intern-events ws zs ps dicts nil 0 fn-arena)
      (if (eq rows :bad)
          (mv :bad fn-arena)
        (mv (revappend rows acc) fn-arena)))))

; -----------------------------------------------------------------------------
; 10. The refinement: the replay with compressed extents is the resident
; replay.

(defthm fn-lzr-cat-intern-lz-refines
  (implies (and (fn-arena-p fn-arena)
                (equal (fn-lzr-lz-value dict (fn-durable-octets (nth 0 x) (nth 3 x) (nth 4 x))
                                        (nth 6 x))
                       (fn-record-payload w)))
           (equal (fn-lzr-cat-intern-lz w x dict keyring generation fn-arena)
                  (fn-cat-intern-list w keyring generation fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-cat-intern-list)
                                  (fn-record-p fn-held-facts-of fn-held-context-of)))))

(defthm fn-lzr-intern-event-refines
  (implies (and (fn-arena-p fn-arena)
                (equal (fn-durable-octets (nfix file) (nfix (nth 2 position)) (len z)) z))
           (equal (fn-lzr-intern-event w z position file dicts keyring generation fn-arena)
                  (fn-intern-event w keyring generation fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-intern-event)
                                  (fn-lzr-cat-intern-lz fn-cat-intern-list fn-arx-intern-event
                                   fn-stxa-p fn-replay-composite-record fn-lzr-extent-of-lz-value
                                   fn-record-p fn-cbor-octet-listp fn-lzr-cat-intern-lz-refines
                                   fn-arx-intern-event-refines fn-durable-octets-len len))
           :do-not-induct t
           :use ((:instance fn-lzr-extent-of-lz-value (payload (fn-record-payload w)))
                 (:instance fn-lzr-cat-intern-lz-refines
                            (x (fn-lzr-extent-of file position z (fn-record-payload w) dicts))
                            (dict (cdr (assoc-equal
                                        (nth 7 (fn-lzr-extent-of file position z
                                                                 (fn-record-payload w) dicts))
                                        dicts))))
                 (:instance fn-arx-intern-event-refines (r z))))))

; With no place the event is the resident one, with no hypothesis.
(defthm fn-lzr-intern-event-without-place
  (equal (fn-lzr-intern-event w z nil file dicts keyring generation fn-arena)
         (fn-intern-event w keyring generation fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-lzr-extent-of)
                                  (fn-arx-intern-event fn-intern-event fn-lzr-cat-intern-lz)))))

(local
 (defthm fn-lzr-arena-p-of-seal-list
   (implies (and (fn-arena-p fn-arena) (fn-cbor-octet-listp xs))
            (fn-arena-p (fn-arena-seal-list xs fn-arena)))
   :hints (("Goal" :in-theory (enable fn-arena-p-is-payload-listp)))))

(local
 (defthm fn-lzr-record-payload-octets
   (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))

(local
 (defthm fn-lzr-composite-payload-octets
   (implies (fn-record-p (fn-replay-composite-record w))
            (fn-cbor-octet-listp (fn-record-payload (fn-replay-composite-record w))))
   :hints (("Goal" :use ((:instance fn-lzr-record-payload-octets
                                    (w (fn-replay-composite-record w))))))))

(local
 (defthm fn-lzr-arena-p-of-intern-event
   (implies (fn-arena-p fn-arena)
            (fn-arena-p (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
   :hints (("Goal" :in-theory (disable fn-intern-event fn-record-p fn-stxa-p
                                       fn-replay-composite-record fn-arena-seal-list-is-append)))))

(defthm fn-lzr-intern-events-refines
  (implies (and (fn-arena-p fn-arena)
                (fn-arx-faithful-p zs ps))
           (equal (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)
                  (fn-intern-events ws keyring generation fn-arena)))
  :hints (("Goal" :induct (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-lzr-intern-event fn-intern-event fn-intern-event-arena)))))

; KEYSTONE (PRF-326).  The host's chunk step with compressed extents is the
; resident chunk step whenever each record's octets (a frame or a plain
; record) are the durable octets at its place: the same rows, the same
; arena.
(defthm fn-lzr-intern-step-refines
  (implies (and (fn-arena-p fn-arena)
                (fn-arx-faithful-p zs ps))
           (equal (fn-lzr-intern-step acc ws zs ps dicts fn-arena)
                  (fn-srs-intern-step acc ws fn-arena)))
  :hints (("Goal" :in-theory (disable fn-lzr-intern-events fn-intern-events))))

; -----------------------------------------------------------------------------
; 11. The commit's reseat of a compressed record.
;
; At the batch's COMPLETE the owner re-points each fenced member's handle at
; the log (host/native/io.lisp fnn-log-reseat-fenced).  A member whose
; record the log holds as a frame is re-pointed at the frame's block when
; the block decodes to the handle's payload (the check reads the arena's
; payload of H and runs the decoder: nothing trusts the host's pairing);
; any other member takes the plain reseat (books/payload-commit-extent.lisp).

(defthm fn-lzr-extentp-lz-guardp
  (implies (and (fn-lzr-extentp e) (fn-cbor-octet-listp d))
           (fn-arn-lz-guardp (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e)
                             (nth 6 e) d))
  :hints (("Goal" :in-theory (enable fn-arn-lz-guardp))))

(defun fn-lzr-commit-reseat (h file position z dicts fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp file) (true-listp position) (true-listp z)
                              (fn-lzr-dictsp dicts))
                  :verify-guards nil))
  (let ((e (and (natp h) (< h (fn-arena-count fn-arena)) (fn-cbor-octet-listp z)
                (fn-lzr-extent-of file position z (fn-arena-payload h fn-arena) dicts))))
    (if e
        (fn-arena-reseat-lz-extent h (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e)
                                   (nth 6 e) (cdr (assoc-equal (nth 7 e) dicts)) fn-arena)
      (fn-arx-commit-reseat h file position z fn-arena))))

(verify-guards fn-lzr-commit-reseat
  :hints (("Goal" :in-theory (disable fn-arx-commit-reseat fn-lzr-extentp fn-arn-lz-guardp
                                      fn-lzr-extent-of fn-arena-payload fn-arena-count
                                      fn-arena-reseat-lz-extent)
           :do-not-induct t
           :use ((:instance fn-lzr-extent-of-extentp (payload (fn-arena-payload h fn-arena)))
                 (:instance fn-lzr-extent-of-dict-octets (payload (fn-arena-payload h fn-arena)))
                 (:instance fn-lzr-extentp-lz-guardp
                            (e (fn-lzr-extent-of file position z (fn-arena-payload h fn-arena) dicts))
                            (d (cdr (assoc-equal
                                     (nth 7 (fn-lzr-extent-of file position z
                                                              (fn-arena-payload h fn-arena) dicts))
                                     dicts))))))))

; The batch: MEMBERS a list of (H FILE POSITION Z) in the log's order.
(defun fn-lzr-commit-reseats (members dicts fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-lzr-dictsp dicts)))
  (if (atom members)
      fn-arena
    (let* ((m (car members))
           (fn-arena (if (and (true-listp m) (equal (len m) 4) (natp (nth 1 m))
                              (true-listp (nth 2 m)) (true-listp (nth 3 m)))
                         (fn-lzr-commit-reseat (nth 0 m) (nth 1 m) (nth 2 m) (nth 3 m) dicts
                                               fn-arena)
                       fn-arena)))
      (fn-lzr-commit-reseats (cdr members) dicts fn-arena))))

(defthm fn-lzr-commit-reseat-keeps-the-arena
  (implies (and (fn-arena-p fn-arena)
                (natp file)
                (true-listp z)
                (equal (fn-durable-octets (nfix file) (nfix (nth 2 position)) (len z)) z))
           (equal (fn-lzr-commit-reseat h file position z dicts fn-arena)
                  fn-arena))
  :hints (("Goal" :in-theory (disable fn-arx-commit-reseat fn-lzr-extent-of-lz-value
                                      fn-arena-reseat-lz-extent-keeps-a-faithful-arena
                                      fn-arx-commit-reseat-keeps-the-arena)
           :do-not-induct t
           :use ((:instance fn-lzr-extent-of-lz-value (payload (fn-arena-payload h fn-arena)))
                 (:instance fn-arena-reseat-lz-extent-keeps-a-faithful-arena
                            (file (nth 0 (fn-lzr-extent-of file position z
                                                           (fn-arena-payload h fn-arena) dicts)))
                            (eoff (nth 1 (fn-lzr-extent-of file position z
                                                           (fn-arena-payload h fn-arena) dicts)))
                            (elen (nth 2 (fn-lzr-extent-of file position z
                                                           (fn-arena-payload h fn-arena) dicts)))
                            (poff (nth 3 (fn-lzr-extent-of file position z
                                                           (fn-arena-payload h fn-arena) dicts)))
                            (plen (nth 4 (fn-lzr-extent-of file position z
                                                           (fn-arena-payload h fn-arena) dicts)))
                            (trailer (nth 5 (fn-lzr-extent-of file position z
                                                              (fn-arena-payload h fn-arena) dicts)))
                            (n (nth 6 (fn-lzr-extent-of file position z
                                                        (fn-arena-payload h fn-arena) dicts)))
                            (dict (cdr (assoc-equal
                                        (nth 7 (fn-lzr-extent-of file position z
                                                                 (fn-arena-payload h fn-arena)
                                                                 dicts))
                                        dicts))))
                 (:instance fn-arx-commit-reseat-keeps-the-arena (r z))))))

; KEYSTONE (PRF-326).  The batch the host reseats with compressed records:
; every member faithful at its place, the arena is unchanged.
(defthm fn-lzr-commit-reseats-keep-the-arena
  (implies (and (fn-arena-p fn-arena)
                (fn-arx-commit-faithful-p members))
           (equal (fn-lzr-commit-reseats members dicts fn-arena)
                  fn-arena))
  :hints (("Goal" :induct (fn-lzr-commit-reseats members dicts fn-arena)
           :in-theory (disable fn-lzr-commit-reseat))))

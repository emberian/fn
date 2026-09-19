; fn C2-04: what replaying the fragment journal proves.
;
; Keystones (each has a reachable witness and per-hypothesis teeth in
; tests/acl2/transfer-journal-tests.lisp):
;   fn-tj-replay-of-journal-is-run           replay(journal) = fold of the transitions
;   fn-tj-replay-sealed-journal-is-run       the same through sealed frames (A-CRYPTO)
;   fn-tj-corrupt-frame-ends-replay-at-typed-fault
;   fn-tj-refused-record-replays-to-same-state
;   fn-tj-run-preserves-statep               the fold never leaves the kernel's states
;   fn-tj-decode-of-encode, fn-tj-open-of-seal   the frame family, both directions
;   fn-tj-replay-frames-with-is-replay-frames the host entry point is the specification
; Corollaries named as such: fn-tj-restart-reproduces-missing-ranges,
; fn-tj-candidate-is-unverified-by-definition.

(in-package "ACL2")
(include-book "transfer-journal")
(include-book "transfer-invariants")
(include-book "frame-invariants")
(local (include-book "arithmetic/top" :dir :system))

; This book opens the frame codec and this cluster's own definitions one layer
; at a time; both are withdrawn at their export theories (BOARD, 2026-09-19
; codecs; the export theory of `books/transfer-journal.lisp`).  Every enable
; here is local: no includer inherits a frame or `fn-tj-` definition rune.
; The full frame vocabulary is opened here and nowhere else: this book has no
; `defun` but `fn-tj-induct`, so the `len`-backchaining cascade cannot reach
; an admission the way it did in `books/transfer-journal.lisp`.
(local (in-theory (enable fn-frame-octet-vocabulary fn-frame-fields-vocabulary
                          fn-frame-record-vocabulary fn-frame-codec-vocabulary
                          fn-frame-invariants-vocabulary fn-tj-vocabulary)))

; The kernel transitions and the record accessors stay closed unless a proof
; opens them: every fact below is about the shape of a record or the value of
; a transition, never about the inside of `fn-transfer-add-chunk`.
(local
 (in-theory (disable fn-tj-kind fn-tj-label fn-tj-arg fn-tj-octets
                     fn-tj-outcome fn-tj-transition-recordp fn-tj-write
                     fn-tj-transition fn-tj-apply
                     fn-transfer-reserve fn-transfer-add-chunk
                     fn-transfer-statep fn-transfer-result-state
                     fn-transfer-result-outcome fn-transfer-missing-ranges)))

; -----------------------------------------------------------------------------
; Record shape facts.  A written record is a transition record whose fields
; are the input's fields and whose outcome is the kernel's.

(defthm fn-tj-write-is-transition-record
  (fn-tj-transition-recordp (fn-tj-write st input))
  :hints (("Goal" :in-theory (enable fn-tj-write fn-tj-transition-recordp
                                      fn-tj-kind fn-frame-item))))

(local
 (defthm fn-tj-write-is-consp
   (consp (fn-tj-write st input))
   :hints (("Goal" :in-theory (enable fn-tj-write)))))

(defthm fn-tj-transition-of-write
  (equal (fn-tj-transition st (fn-tj-write st input))
         (fn-tj-transition st input))
  :hints (("Goal" :in-theory (enable fn-tj-write fn-tj-transition fn-tj-kind
                                      fn-tj-label fn-tj-arg fn-tj-octets
                                      fn-frame-item))))

(defthm fn-tj-write-records-the-kernel-outcome
  (equal (fn-tj-outcome (fn-tj-write st input))
         (fn-transfer-result-outcome (fn-tj-transition st input)))
  :hints (("Goal" :in-theory (enable fn-tj-write fn-tj-outcome fn-tj-kind
                                      fn-frame-item))))

(defthm fn-tj-apply-of-write
  (equal (fn-tj-apply st (fn-tj-write st input))
         (list :ok (fn-transfer-result-state (fn-tj-transition st input))))
  :hints (("Goal" :in-theory (enable fn-tj-apply))))

; -----------------------------------------------------------------------------
; KEYSTONE: replay of the journal is the fold of the transitions, for any
; state and any input list whatsoever.  A malformed input is journaled with
; the refusal the kernel gave it and replays to the same refusal.

(defun fn-tj-induct (st inputs index)
  (if (consp inputs)
      (fn-tj-induct (fn-transfer-result-state (fn-tj-transition st (car inputs)))
                    (cdr inputs) (+ 1 index))
    (list st index)))

(defthm fn-tj-replay-of-journal-is-run
  (implies (natp index)
           (equal (fn-tj-replay-records st (fn-tj-journal st inputs) index)
                  (list :ok (fn-tj-run st inputs) (+ (len inputs) index))))
  :hints (("Goal" :induct (fn-tj-induct st inputs index)
           :in-theory (enable fn-tj-replay-records fn-tj-journal fn-tj-run))))

; One step first, with the kernel closed: the dispatch opens to exactly the
; two public transitions and each is discharged by the kernel's own exported
; preservation keystone (`fn-transfer-reserve-preserves-statep`,
; `books/transfer-reservation.lisp`; `fn-transfer-add-chunk-preserves-statep`,
; `books/transfer-invariants.lisp`).  Opening `fn-tj-transition` inside the
; induction instead sent the waterfall into `GENERALIZE-CLAUSE` on the
; arithmetic library's `floor`/`mod` rules and aborted (measured here).
(local
 (defthm fn-tj-transition-preserves-statep
   (implies (fn-transfer-statep st)
            (fn-transfer-statep
             (fn-transfer-result-state (fn-tj-transition st r))))
   ; `fn-transfer-add-chunk-result-state-normal-form` is exported enabled by
   ; `books/transfer-invariants.lisp` and rewrites the stored branch into its
   ; explicit `(list (car st) (fn-transfer-replace-entry-with-chunks ...))`
   ; before the preservation keystone can fire, which is what left the
   ; add-chunk branch open here.  Both keystones are cited by `:use` with the
   ; normal form closed.
   :hints (("Goal" :do-not '(generalize)
            :use ((:instance fn-transfer-reserve-preserves-statep
                             (label (fn-tj-label r))
                             (declared-length (fn-tj-arg r)))
                  (:instance fn-transfer-add-chunk-preserves-statep
                             (label (fn-tj-label r)) (offset (fn-tj-arg r))
                             (octets (fn-tj-octets r))))
            :in-theory (e/d (fn-tj-transition)
                            (fn-transfer-add-chunk-result-state-normal-form
                             fn-transfer-reserve-preserves-statep
                             fn-transfer-add-chunk-preserves-statep))))))

; The fold never leaves the kernel's own states: whatever a replay reaches
; is a state the two public transitions built.
(defthm fn-tj-run-preserves-statep
  (implies (fn-transfer-statep st)
           (fn-transfer-statep (fn-tj-run st inputs)))
  :hints (("Goal" :induct (fn-tj-run st inputs)
           :do-not '(generalize)
           :in-theory (e/d (fn-tj-run) (fn-tj-transition)))))

; Corollary of the keystone (docs/proof-style.md §7): after a restart the
; kernel reports the same missing ranges for every label, because it is the
; same state.  It is `:rule-classes nil` and is cited by `:use`, never
; enabled; it is not a registry event, the keystone above it is.
(defthm fn-tj-restart-reproduces-missing-ranges
  (implies (natp index)
           (equal (fn-transfer-missing-ranges
                   (fn-frame-item 1 (fn-tj-replay-records
                                     st (fn-tj-journal st inputs) index))
                   label)
                  (fn-transfer-missing-ranges (fn-tj-run st inputs) label)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-tj-replay-records fn-tj-journal
                                      fn-tj-run))))

; -----------------------------------------------------------------------------
; Frames: the sealed record opens to itself.

(local
 (defthm fn-tj-code-natp
   (natp (fn-tj-code r))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-tj-code fn-frame-enum-index)))))

(local
 (defthm fn-tj-code-bound
   (<= (fn-tj-code r) 3)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-tj-code fn-frame-enum-index)))))

(local
 (defthm fn-tj-record-okp-spec
   (implies (fn-tj-record-okp r)
            (not (equal (fn-tj-spec-for (fn-tj-kind r)) :none)))
   :hints (("Goal" :in-theory (enable fn-tj-record-okp)))))

(local
 (defthm fn-tj-record-okp-code-positive
   (implies (fn-tj-record-okp r)
            (< 0 (fn-tj-code r)))
   :rule-classes (:rewrite :linear)
   :hints (("Goal" :in-theory (enable fn-tj-record-okp fn-tj-code fn-tj-spec-for
                                       fn-frame-enum-index)))))

(local
 (defthm fn-tj-record-okp-code-not-zero
   (implies (fn-tj-record-okp r)
            (not (equal (fn-tj-code r) 0)))
   :hints (("Goal" :use fn-tj-record-okp-code-positive
            :in-theory (disable fn-tj-record-okp-code-positive)))))

(local
 (defthm fn-tj-record-okp-kind-of-code
   (implies (fn-tj-record-okp r)
            (equal (fn-frame-item (+ -1 (fn-tj-code r)) *fn-tj-kinds*)
                   (fn-tj-kind r)))
   :hints (("Goal" :in-theory (enable fn-tj-record-okp fn-tj-code fn-tj-spec-for
                                       fn-frame-enum-index fn-frame-item)))))

(local
 (defthm fn-tj-payload-is-octets
   (implies (fn-tj-record-okp r)
            (fn-cbor-octet-listp (fn-tj-payload r)))
   :hints (("Goal" :in-theory (e/d (fn-tj-payload fn-tj-record-okp)
                                   (fn-frame-fields-octets))))))

(local
 (defthm fn-tj-payload-bound
   (implies (fn-tj-record-okp r)
            (<= (len (fn-tj-payload r)) *fn-tj-max-payload*))
   :rule-classes (:rewrite :linear)
   :hints (("Goal" :in-theory (e/d (fn-tj-payload fn-tj-record-okp)
                                   (fn-frame-fields-octets))))))

(local
 (defthm fn-tj-record-okp-is-frame-input
   (implies (fn-tj-record-okp r)
            (fn-frame-inputp *fn-tj-magic* *fn-tj-version* (fn-tj-code r)
                             (fn-tj-payload r) *fn-tj-max-payload*))
   :hints (("Goal" :in-theory (e/d (fn-frame-inputp fn-frame-magicp
                                    fn-cbor-octetp)
                                   (fn-tj-payload fn-tj-code
                                    fn-tj-record-okp))))))

(local
 (defthm fn-tj-fields-parse-of-payload
   (implies (fn-tj-record-okp r)
            (equal (fn-frame-fields-parse (fn-tj-spec-for (fn-tj-kind r))
                                          (fn-tj-payload r))
                   (fn-frame-parse-ok (cdr r) nil)))
   :hints (("Goal" :in-theory (e/d (fn-tj-payload fn-tj-record-okp)
                                   (fn-frame-fields-octets
                                    fn-frame-fields-parse
                                    fn-frame-fields-parse-aux))))))

(local
 (defthm fn-tj-encode-unfolds
   (implies (and (fn-tj-record-okp r) (fn-frame-digestp digest))
            (equal (fn-tj-encode r digest)
                   (fn-frame-encode *fn-tj-magic* *fn-tj-version*
                                    (fn-tj-code r) (fn-tj-payload r) digest)))
   :hints (("Goal" :in-theory (e/d (fn-tj-encode)
                                   (fn-frame-encode fn-tj-code fn-tj-payload
                                    fn-tj-record-okp fn-frame-digestp))))))

(defthm fn-tj-decode-of-encode
  (implies (and (fn-tj-record-okp r)
                (fn-frame-digestp digest))
           (equal (fn-tj-decode (fn-tj-encode r digest) digest)
                  (fn-frame-ok *fn-tj-magic* *fn-tj-version*
                               (fn-tj-kind r) (cdr r))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-tj-decode fn-frame-result-okp
                            fn-frame-result-magic fn-frame-result-version
                            fn-frame-result-kind fn-frame-result-payload
                            fn-frame-ok fn-frame-error fn-frame-item)
                           (fn-tj-encode fn-frame-decode fn-frame-encode
                            fn-frame-fields-parse fn-frame-fields-parse-aux
                            fn-frame-fields-octets fn-tj-code fn-tj-payload
                            fn-tj-record-okp fn-frame-inputp fn-frame-digestp
                            fn-frame-parse-ok fn-frame-parse-okp
                            fn-frame-parse-value)))))

(local
 (defthm fn-tj-protected-prefix-of-encode
   (implies (and (fn-tj-record-okp r) (fn-frame-digestp digest))
            (equal (fn-frame-protected-prefix (fn-tj-encode r digest))
                   (fn-frame-protected *fn-tj-magic* *fn-tj-version*
                                       (fn-tj-code r) (fn-tj-payload r))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-frame-protected-prefix-of-encode
                             (magic *fn-tj-magic*) (version *fn-tj-version*)
                             (kind (fn-tj-code r)) (payload (fn-tj-payload r))
                             (max-payload *fn-tj-max-payload*))
                  (:instance fn-tj-record-okp-is-frame-input))
            :in-theory (e/d ()
                            (fn-frame-encode fn-frame-protected
                             fn-frame-protected-prefix fn-tj-code fn-tj-payload
                             fn-tj-record-okp fn-frame-inputp fn-frame-digestp
                             fn-frame-protected-prefix-of-encode
                             fn-tj-record-okp-is-frame-input
                             fn-tj-encode))))))

(defthm fn-tj-open-of-seal
  (implies (fn-tj-record-okp r)
           (equal (fn-tj-open (fn-tj-seal r))
                  (fn-frame-ok *fn-tj-magic* *fn-tj-version*
                               (fn-tj-kind r) (cdr r))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-tj-open fn-tj-seal)
                           (fn-tj-decode fn-tj-encode fn-tj-payload fn-tj-code
                            fn-tj-record-okp fn-frame-protected
                            fn-frame-protected-prefix fn-frame-encode
                            fn-tj-encode-unfolds fn-frame-digestp)))))

(local
 (defthm fn-tj-result-okp-of-ok
   (fn-frame-result-okp (fn-frame-ok m v kind values))
   :hints (("Goal" :in-theory (enable fn-frame-result-okp fn-frame-ok)))))

(local
 (defthm fn-tj-frame-record-of-ok
   (equal (fn-tj-frame-record (fn-frame-ok m v kind values))
          (cons kind values))
   :hints (("Goal" :in-theory (enable fn-tj-frame-record fn-frame-ok
                                       fn-frame-result-kind
                                       fn-frame-result-payload fn-frame-item)))))

(local
 (defthm fn-tj-cons-kind-cdr
   (implies (consp r)
            (equal (cons (fn-tj-kind r) (cdr r)) r))
   :hints (("Goal" :in-theory (enable fn-tj-kind fn-frame-item)))))

; KEYSTONE under A-CRYPTO: replay of the sealed journal is the fold.
(defthm fn-tj-replay-sealed-journal-is-run
  (implies (and (natp index)
                (fn-tj-records-okp (fn-tj-journal st inputs)))
           (equal (fn-tj-replay-frames
                   st (fn-tj-seal-journal (fn-tj-journal st inputs)) index)
                  (list :ok (fn-tj-run st inputs) (+ (len inputs) index))))
  :hints (("Goal" :induct (fn-tj-induct st inputs index)
           :in-theory (e/d (fn-tj-replay-frames fn-tj-seal-journal
                            fn-tj-journal fn-tj-run fn-tj-records-okp)
                           (fn-tj-open fn-tj-seal fn-tj-record-okp
                            fn-tj-frame-record fn-frame-result-okp
                            fn-frame-ok)))))

; -----------------------------------------------------------------------------
; KEYSTONE: a frame that does not open ends replay at a typed fault with the
; state of the good prefix.  Nothing of the bad frame reaches the state.

(local
 (defthm fn-tj-replay-frames-of-append
   (implies (natp index)
            (equal (fn-tj-replay-frames st (append xs ys) index)
                   (let ((first (fn-tj-replay-frames st xs index)))
                     (if (equal (fn-frame-item 0 first) :ok)
                         (fn-tj-replay-frames (fn-frame-item 1 first) ys
                                              (fn-frame-item 2 first))
                       first))))
   :hints (("Goal" :induct (fn-tj-replay-frames st xs index)
            :in-theory (e/d (fn-tj-replay-frames fn-frame-item)
                            (fn-tj-open fn-tj-frame-record
                             fn-frame-result-okp))))))

(defthm fn-tj-corrupt-frame-ends-replay-at-typed-fault
  (implies (and (natp index)
                (fn-tj-records-okp (fn-tj-journal st inputs))
                (not (fn-frame-result-okp (fn-tj-open bad))))
           (equal (fn-tj-replay-frames
                   st
                   (append (fn-tj-seal-journal (fn-tj-journal st inputs))
                           (cons bad rest))
                   index)
                  (list :fault
                        (list :corrupt (fn-frame-item 1 (fn-tj-open bad)))
                        (fn-tj-run st inputs)
                        (+ (len inputs) index))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-item)
                           (fn-tj-open fn-tj-frame-record
                            fn-frame-result-okp fn-tj-seal-journal
                            fn-tj-journal fn-tj-run))
           :expand ((fn-tj-replay-frames (fn-tj-run st inputs)
                                         (cons bad rest)
                                         (+ (len inputs) index))))))

; -----------------------------------------------------------------------------
; KEYSTONE: a journaled refusal replays to exactly the prior state.  This
; covers `:duplicate`, `:covered`, every `:overlap-conflict` (a differing byte
; is refused before any octet is retained) and every resource refusal.  The
; two acceptance outcomes are the only records that can move the state.

(local
 (defthm fn-tj-add-chunk-on-non-state-no-overwrite
   (implies (not (fn-transfer-statep st))
            (equal (fn-transfer-result-state
                    (fn-transfer-add-chunk st label offset octets))
                   st))
   :hints (("Goal" :in-theory (e/d (fn-transfer-add-chunk
                                    fn-transfer-result-state)
                                   (fn-transfer-statep))))))

(defthm fn-tj-refused-record-replays-to-same-state
  (implies (and (not (equal (fn-tj-outcome r) :reserved))
                (not (equal (fn-tj-outcome r) :stored)))
           (equal (fn-frame-item 1 (fn-tj-apply st r)) st))
  ; Same trap as `fn-tj-transition-preserves-statep`: `books/transfer-
  ; invariants.lisp` exports `fn-transfer-add-chunk-result-state-normal-form`
  ; enabled, and it rewrites the stored branch into its explicit
  ; `(list (car st) (fn-transfer-replace-entry-with-chunks ...))` before the
  ; three refusal lemmas cited below can meet the goal.  Both it and
  ; `fn-transfer-find-absent-is-nil` are closed here.  A board CHANGE-request
  ; asks nntp to make the normal form `:rule-classes nil`.
  :hints (("Goal" :in-theory (e/d (fn-tj-apply fn-tj-transition fn-frame-item)
                                  (fn-transfer-add-chunk-result-state-normal-form
                                   fn-transfer-find-absent-is-nil))
           :use ((:instance fn-transfer-reserve-refusal-no-overwrite-general
                            (label (fn-tj-label r))
                            (declared-length (fn-tj-arg r)))
                 (:instance fn-transfer-reserve-refusal-no-overwrite
                            (label (fn-tj-label r))
                            (declared-length (fn-tj-arg r)))
                 (:instance fn-transfer-add-chunk-refusal-or-conflict-no-overwrite
                            (label (fn-tj-label r))
                            (offset (fn-tj-arg r))
                            (octets (fn-tj-octets r)))
                 (:instance fn-tj-add-chunk-on-non-state-no-overwrite
                            (label (fn-tj-label r))
                            (offset (fn-tj-arg r))
                            (octets (fn-tj-octets r)))))))

; -----------------------------------------------------------------------------
; The host entry point is the specification: with the digests a correct host
; supplies, `fn-tj-replay-frames-with` is `fn-tj-replay-frames`.

(defthm fn-tj-replay-frames-with-is-replay-frames
  (implies (equal digests (fn-tj-digests-of frames))
           (equal (fn-tj-replay-frames-with st frames digests index)
                  (fn-tj-replay-frames st frames index)))
  :hints (("Goal" :induct (fn-tj-replay-frames-with st frames digests index)
           :in-theory (e/d (fn-tj-replay-frames-with fn-tj-replay-frames
                            fn-tj-digests-of fn-tj-open)
                           (fn-tj-decode fn-tj-frame-record
                            fn-frame-result-okp)))))

; -----------------------------------------------------------------------------
; By definition: the only export of a complete entry is tagged :unverified.

; `-by-definition`: this restates the tag the one non-nil branch of
; `fn-tj-candidate` builds.  `:rule-classes nil` (docs/proof-style.md §7); it
; is not a registry event.
(defthm fn-tj-candidate-is-unverified-by-definition
  (implies (fn-tj-candidate st label)
           (equal (car (fn-tj-candidate st label)) :unverified))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-tj-candidate))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md §2).  The keystones leave this book
; enabled; the record-shape facts about a written record are proof vocabulary
; and are withdrawn under one name.

(deftheory fn-tj-invariants-vocabulary
  '(fn-tj-write-is-transition-record fn-tj-transition-of-write
    fn-tj-write-records-the-kernel-outcome fn-tj-apply-of-write))

(in-theory (disable fn-tj-invariants-vocabulary))

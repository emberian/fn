; host/spike-storage-fast-host.lisp -- spike/storage (D28): replay without
; per-event whole-state revalidation.  ld'ed by host/native/build.lisp before
; host/store-node-host.lisp, whose open wrappers call these.
;
; Measured (hbox, N=300, logs/sprof-full300.txt): 76% of a full-replay open
; is fn-node-statep, called four times per replayed event by fn-cpr-loop and
; fn-cpr-apply-event (books/config-physical-replay.lisp), and fn-node-statep
; is itself quadratic (binding/article subset checks by member).  So the open
; is Theta(N^3).  AGENTS.md: "carry the invariant in state and prove it
; preserved".
;
;; SPIKE: defers, for dev to prove (book above config-physical-replay):
;;  1. fn-replay-apply-record-preserves-node-statep: (fn-node-statep n) and
;;     (consp (fn-replay-apply-record n e)) imply the result is fn-node-statep
;;     (node-config.lisp has it for fn-cnode-apply-record).
;;  2. fn-spk-cpr-fold-equals-cpr-loop: under (fn-cnode-statep cn),
;;     (fn-spk-cpr-fold cn configs events cs es nil) = (fn-cpr-loop ...), and
;;     with PAUSE = t it equals fn-sco-cpr-prefix.  By induction with 1 and
;;     fn-cnode-apply-config's preservation.
;;  3. The once-per-open recognizers dropped here (fn-cnode-statep at the
;;     finish, fn-sn-statep of the opened state) are implied by 2 and the
;;     existing open theorems; the spike does not run them.

(in-package "ACL2")
; The books host/store-node-host.lisp includes (P3 adds the checkpoint ones).
(include-book "../books/store-observed")
(include-book "../books/poster-bytes")
(include-book "../books/native-config-observation")
(include-book "../books/store-sweep")
(include-book "../books/store-node-resolution")
(include-book "../books/store-prepare-correspondence")
(include-book "../books/store-budget")
(include-book "../books/node-config")
(include-book "../books/native-admin")
(include-book "../books/store-checkpoint-open")
(include-book "../books/store-checkpoint-codec")
(include-book "../books/byte-store-state-checkpoint-program")
(include-book "../books/peer-config")
(include-book "../books/provenance-codec")

(defun fn-spk-apply-event (cn event)
  (declare (xargs :mode :program))
  (if (and (fn-store-event-p event) (fn-cpr-event-servedp cn event))
      (let ((next (fn-replay-apply-record (fn-cnode-node cn) event)))
        (if (consp next) (fn-cnode-make next (fn-cnode-config cn)) nil))
    nil))

; The fold of fn-cpr-loop (PAUSE nil) or fn-sco-cpr-prefix (PAUSE t), with
; the whole-state recognizer run on configuration steps only (rare), never
; per event.  The caller establishes (fn-cnode-statep cn) once.
(defun fn-spk-cpr-fold (cn configs events config-sequence event-sequence pause)
  (declare (xargs :mode :program))
  (if (and pause (not (consp events)))
      (fn-sco-paused cn config-sequence event-sequence)
    (let ((position (+ (nfix config-sequence) (nfix event-sequence))))
      (if (fn-cpr-config-firstp configs events)
          (let* ((record (car configs))
                 (txid (fn-cfg-record-txid record))
                 (node (fn-cnode-node cn)))
            (cond ((not (fn-cfg-recordp record))
                   (fn-replay-fault cn position :invalid-config-record))
                  ((not (equal (fn-cfg-record-sequence record) config-sequence))
                   (fn-replay-fault cn position :config-sequence))
                  ((not (fn-replay-advance-okp node txid))
                   (fn-replay-fault cn position :config-txid))
                  (t (let ((at (fn-cnode-make
                                (fn-replay-advance-txid node txid)
                                (fn-cnode-config cn))))
                       (if (not (fn-cnode-record-acceptablep
                                 at record (fn-cnode-line-ceiling)))
                           (fn-replay-fault cn position :config-refusal)
                         (fn-spk-cpr-fold
                          (fn-cnode-apply-config at record (fn-cnode-line-ceiling))
                          (cdr configs) events
                          (+ 1 (nfix config-sequence)) event-sequence pause))))))
        (if (consp events)
            (let ((event (car events)))
              (cond ((not (fn-store-event-p event))
                     (fn-replay-fault cn position :invalid-event))
                    ((not (equal (fn-store-event-sequence event) event-sequence))
                     (fn-replay-fault cn position :event-sequence))
                    (t (let ((next (fn-spk-apply-event cn event)))
                         (if (not (consp next))
                             (fn-replay-fault cn position :event-refusal)
                           (fn-spk-cpr-fold next configs (cdr events)
                                            config-sequence
                                            (+ 1 (nfix event-sequence)) pause))))))
          (if (and (null configs) (null events))
              (fn-replay-ok cn position)
            (fn-replay-fault cn position :improper-history)))))))

(defun fn-spk-cpr-start (cn configs events cs es pause)
  (declare (xargs :mode :program))
  (if (not (fn-cnode-statep cn))
      (fn-replay-fault cn (+ (nfix cs) (nfix es)) :invalid-node)
    (fn-spk-cpr-fold cn configs events cs es pause)))

(defun fn-spk-cpr-replay (configs events)
  (declare (xargs :mode :program))
  (fn-spk-cpr-start (fn-cnode-initial (fn-cfg-initial)) configs events 0 0 nil))

; fn-cpo-open-observed with the fast fold and without the closing recognizers.
(defun fn-spk-open-tail (configs frontier events cn identity consumer topic event-index)
  (declare (xargs :mode :program))
  (let ((node (fn-cnode-node cn)))
    (if (not (fn-replay-advance-okp node frontier))
        (fn-sn-open-error :frontier)
      (let* ((advanced (fn-replay-advance-txid node frontier))
             (config (fn-cnode-config cn))
             (files (fn-sf-make :recovering frontier nil events nil nil nil 0))
             (seed (fn-sn-observed-seed (fn-cnode-domain-of config)
                                        (fn-cfg-capacity (fn-cfg-value config))
                                        frontier events))
             (opened (fn-sn-with-event-index
                      (fn-sn-with-topic
                       (fn-sn-with-consumer
                        (fn-cpo-install
                         (fn-sn-update-replayed
                          seed files advanced
                          (fn-stx-index-of-store (fn-stx-store advanced) nil)
                          identity)
                         (fn-cnode-make advanced config) configs)
                        (fn-cp-nth 1 consumer))
                       topic)
                      event-index)))
        (if (and (equal (fn-stxk-context-kind identity) :ok)
                 (consp consumer) (eq (car consumer) :ok)
                 (eq (fn-th-at 0 topic) :ok))
            (fn-sn-open-ok opened)
          (fn-sn-open-error :identity))))))

(defun fn-spk-cpo-open-observed (configs frontier events)
  (declare (xargs :mode :program))
  (if (or (null configs) (not (fn-sn-observed-historyp frontier events)))
      (fn-sn-open-error :history)
    (let ((replayed (fn-spk-cpr-replay configs events)))
      (if (not (equal (fn-replay-result-kind replayed) :ok))
          (fn-sn-open-error :replay)
        (fn-spk-open-tail configs frontier events
                          (fn-replay-result-node replayed)
                          (fn-replay-identity events)
                          (fn-cpe-projection-replay nil events 0)
                          (fn-th-prefix-project events)
                          (fn-cei-build events))))))

; P3's checkpoint folds over the fast fold.
(defun fn-spk-sco-capture (configs records)
  (declare (xargs :mode :program))
  (let ((records (true-list-fix records)))
    (fn-sco-make records
                 (fn-spk-cpr-start (fn-cnode-initial (fn-cfg-initial))
                                   configs records 0 0 t)
                 (fn-replay-identity-loop records (fn-stxk-initial-context 0))
                 (fn-cpe-projection-replay nil records 0)
                 (fn-th-prefix-loop (fn-th-prefix-state :ok 0 nil nil nil nil nil)
                                    records)
                 (fn-cei-build-aux records 0 nil))))

(defun fn-spk-sco-cpr-resume (r configs events)
  (declare (xargs :mode :program))
  (if (fn-sco-pausedp r)
      (let ((cs (fn-sco-at 2 r)))
        (fn-spk-cpr-start (fn-sco-at 1 r) (fn-sco-nthcdr (nfix cs) configs) events
                          cs (fn-sco-at 3 r) t))
    r))

(defun fn-spk-sco-cpr-finish (r configs)
  (declare (xargs :mode :program))
  (if (fn-sco-pausedp r)
      (let ((cs (fn-sco-at 2 r)))
        (fn-spk-cpr-fold (fn-sco-at 1 r) (fn-sco-nthcdr (nfix cs) configs) nil
                         cs (fn-sco-at 3 r) nil))
    r))

(defun fn-spk-sco-extend (c configs suffix)
  (declare (xargs :mode :program))
  (let ((records (true-list-fix (fn-sco-records c))))
    (fn-sco-make (append records suffix)
                 (fn-spk-sco-cpr-resume (fn-sco-cpr c) configs suffix)
                 (fn-replay-identity-loop suffix (fn-sco-identity c))
                 (fn-sco-consumer-resume (fn-sco-consumer c) suffix (len records))
                 (fn-th-prefix-loop (fn-sco-topic c) suffix)
                 (fn-cei-build-aux suffix (len records) (fn-sco-event-index c)))))

(defun fn-spk-sco-finalize (c configs frontier)
  (declare (xargs :mode :program))
  (let ((events (fn-sco-records c)))
    (if (or (null configs) (not (fn-sn-observed-historyp frontier events)))
        (fn-sn-open-error :history)
      (let ((replayed (fn-spk-sco-cpr-finish (fn-sco-cpr c) configs)))
        (if (not (equal (fn-replay-result-kind replayed) :ok))
            (fn-sn-open-error :replay)
          (fn-spk-open-tail configs frontier events
                            (fn-replay-result-node replayed)
                            (fn-sco-identity c) (fn-sco-consumer c)
                            (fn-sco-topic c) (fn-sco-event-index c)))))))

(defun fn-spk-sco-open (c configs frontier suffix)
  (declare (xargs :mode :program))
  (fn-spk-sco-finalize (fn-spk-sco-extend c configs suffix) configs frontier))

(defun fn-spk-sco-replay-result (c configs suffix)
  (declare (xargs :mode :program))
  (fn-spk-sco-cpr-finish (fn-spk-sco-cpr-resume (fn-sco-cpr c) configs suffix)
                         configs))

; The open result's kind without fn-sn-open-okp's fn-sn-statep.
(defun fn-spk-open-okp (opened)
  (declare (xargs :mode :program))
  (and (fn-sn-open-shapep opened) (equal (fn-sn-open-kind opened) :ok)))

; -----------------------------------------------------------------------------
; C1. The reclaimed-content stub and the D25 decision over it.
;
; A reclaimed article's payload becomes a stub: its header block verbatim,
; then one line `FN-Reclaimed: v1 octets=N sha256=H source=S' and an empty
; body.  H is fn-frame-digest (SHA-256) of the whole original payload; S is
; the digest of the poster's source (books/poster-bytes fn-pb-subject under
; the article's own Path agent), or `-' when that recipe gives none.
;
;; SPIKE: defers (a) the stub codec as a book with its round trip
;; (fn-spk-stub-info of fn-spk-stub gives back octets, H and S); (b) the D25
;; keystone fn-spk-same-articlep-equals-original: for every submission,
;; fn-spk-same-articlep against the stub equals fn-pb-same-articlep against
;; the original, under a named collision assumption A-DIGEST-COLLISION-FREE
;; (constrained, books/assumptions.lisp) and the fact that the injection
;; inverse gives a source only under the article's own agent; (c) refusal of
;; a submission that itself carries an FN-Reclaimed header (the stub marker
;; must be the node's alone; fn-spk-submission-claims-stubp below is checked
;; at the owner's prepare).

(defun fn-spk-octets-of (str)
  (declare (xargs :mode :program))
  (fn-record-string-octets str))

(defun fn-spk-crlf2-index (x i)
  (declare (xargs :mode :program))
  (cond ((atom x) nil)
        ((and (equal (car x) 13) (consp (cdr x)) (equal (cadr x) 10)
              (consp (cddr x)) (equal (caddr x) 13)
              (consp (cdddr x)) (equal (cadddr x) 10))
         i)
        (t (fn-spk-crlf2-index (cdr x) (+ 1 i)))))

(defun fn-spk-header-block (payload)
  ; The octets before the blank line (without its first CRLF's partner).
  (declare (xargs :mode :program))
  (let ((i (fn-spk-crlf2-index payload 0)))
    (if i (take i payload) payload)))

(defun fn-spk-hex-digit (n)
  (declare (xargs :mode :program))
  (if (< n 10) (+ 48 n) (+ 87 n)))

(defun fn-spk-hex (octets)
  (declare (xargs :mode :program))
  (if (atom octets) nil
    (list* (fn-spk-hex-digit (floor (car octets) 16))
           (fn-spk-hex-digit (mod (car octets) 16))
           (fn-spk-hex (cdr octets)))))

(defun fn-spk-nat-digits (n)
  (declare (xargs :mode :program))
  (if (< n 10) (list (+ 48 n))
    (append (fn-spk-nat-digits (floor n 10)) (list (+ 48 (mod n 10))))))

(defun fn-spk-marker () (declare (xargs :mode :program))
  (fn-spk-octets-of "FN-Reclaimed: v1 "))

(defun fn-spk-source-digest (payload msgid)
  ; msgid is the Store's string key.
  (declare (xargs :mode :program))
  (let* ((agent (fn-pb-path-agent payload))
         (subject (fn-pb-subject payload agent (fn-record-string-octets msgid))))
    (if (and agent (equal (car subject) :source))
        (fn-frame-digest (cdr subject))
      nil)))

(defun fn-spk-stub (payload msgid)
  (declare (xargs :mode :program))
  (let ((source (fn-spk-source-digest payload msgid)))
    (append (fn-spk-header-block payload)
            '(13 10)
            (fn-spk-marker)
            (fn-spk-octets-of "octets=") (fn-spk-nat-digits (len payload))
            (fn-spk-octets-of " sha256=") (fn-spk-hex (fn-frame-digest payload))
            (fn-spk-octets-of " source=")
            (if source (fn-spk-hex source) (fn-spk-octets-of "-"))
            '(13 10 13 10))))

(defun fn-spk-prefixp (p x)
  (declare (xargs :mode :program))
  (cond ((atom p) t)
        ((atom x) nil)
        (t (and (equal (car p) (car x)) (fn-spk-prefixp (cdr p) (cdr x))))))

(defun fn-spk-find-line (needle x)
  ; The tail of x after the first CRLF + needle, or nil.
  (declare (xargs :mode :program))
  (cond ((atom x) nil)
        ((and (equal (car x) 13) (consp (cdr x)) (equal (cadr x) 10)
              (fn-spk-prefixp needle (cddr x)))
         (nthcdr (len needle) (cddr x)))
        (t (fn-spk-find-line needle (cdr x)))))

(defun fn-spk-take-token (x)
  ; Octets up to a space or CR.
  (declare (xargs :mode :program))
  (if (or (atom x) (equal (car x) 32) (equal (car x) 13)) nil
    (cons (car x) (fn-spk-take-token (cdr x)))))

(defun fn-spk-field (name x)
  ; The token after `NAME=' in x (one line), or nil.
  (declare (xargs :mode :program))
  (let ((key (append (fn-spk-octets-of name) '(61))))
    (cond ((atom x) nil)
          ((equal (car x) 13) nil)
          ((fn-spk-prefixp key x) (fn-spk-take-token (nthcdr (len key) x)))
          (t (fn-spk-field name (cdr x))))))

; (SHA256-HEX SOURCE-HEX-or-"-" OCTETS-DIGITS) when PAYLOAD is a stub, else nil.
; Only the header block is searched, and the marker must be the last header.
(defun fn-spk-stub-info (payload)
  (declare (xargs :mode :program))
  (let* ((tail (fn-spk-find-line (fn-spk-marker) payload)))
    (and tail
         (let ((sha (fn-spk-field "sha256" tail))
               (src (fn-spk-field "source" tail))
               (n (fn-spk-field "octets" tail)))
           (and sha src n (list sha src n))))))

(defun fn-spk-submission-claims-stubp (payload)
  (declare (xargs :mode :program))
  (if (fn-spk-find-line (fn-spk-marker) (fn-spk-header-block payload)) t nil))

(defun fn-spk-same-articlep (msgid payload held)
  ; msgid: the Store's string key.
  (declare (xargs :mode :program))
  (let ((info (fn-spk-stub-info held)))
    (if (not info)
        (fn-pb-same-articlep (fn-record-string-octets msgid) payload held)
      (let* ((agent (fn-pb-path-agent payload))
             (a (fn-pb-subject payload agent (fn-record-string-octets msgid)))
             (held-agent (fn-pb-path-agent held))
             (source-hex (second info)))
        (if (and (equal (car a) :source) agent (equal agent held-agent)
                 (not (equal source-hex (fn-spk-octets-of "-"))))
            (equal (fn-spk-hex (fn-frame-digest (cdr a))) source-hex)
          (equal (fn-spk-hex (fn-frame-digest payload)) (first info)))))))

; fn-pb-existing-action over the stub-aware comparison.
(defun fn-spk-existing-action (msgid payload groups s)
  (declare (xargs :mode :program))
  (let ((article (fn-find-article
                  msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
    (if article
        (if (and (fn-spk-same-articlep msgid payload (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

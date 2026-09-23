; The actual owner/served reader pins the Store's accepted historical verdict.
; The signed Store event and reopen facts come from the T10a trace, not an
; invented verdict table.  Two readers straddle its durable publication.
(in-package "ACL2")
(include-book "../../books/owner")
(include-book "store-identity-traces-tests")
(include-book "../../books/nntp-verdict-effects")

(defconst *ov-hdr*
  (append (fn-nntp-string-octets
           "HDR :fn-verified <carried@example.invalid>")
          '(13 10)))
(defconst *ov-before* (fn-own-start *sit-after-enrollment* 4))
(defconst *ov-reader-a* (cdr (fn-own-open *ov-before* nil)))
(defconst *ov-writer* (cdr (fn-own-open *ov-reader-a* nil)))
(defconst *ov-begun* (fn-own-step *ov-writer* '(:begin 1)))
(defconst *ov-post-events*
  (list '(:store (:io :start-frontier nil))
        '(:store (:io :frontier-file :ok))
        '(:store (:io :frontier-replace :ok))
        '(:store (:io :frontier-directory :ok))
        (list :store (list :prepare-identity *sit-carried-composite*))
        '(:store (:io :record-file :ok))
        '(:store (:io :record-link :ok))
        '(:store (:io :record-directory :ok))
        '(:complete)))
(make-event `(defconst *ov-posted* ',(fn-own-run *ov-begun* *ov-post-events*)))

; Owner emits the same Store event and pins it only for newly opened readers.
(assert-event (equal (fn-own-store *ov-posted*) *sit-after-carried*))
(assert-event (null (fn-own-conn-verdicts
                     (fn-own-find-conn 0 (fn-own-conns *ov-posted*)))))
(defconst *ov-reader-b* (cdr (fn-own-open *ov-posted* nil)))
(assert-event
 (equal (fn-own-conn-verdicts
         (fn-own-find-conn 2 (fn-own-conns *ov-reader-b*)))
        (fn-sn-verdicts *sit-after-carried*)))

; These replies are produced through the host-called fn-own-read byte fold.
(defconst *ov-read-a* (fn-own-read *ov-reader-b* 0 *ov-hdr*))
(defconst *ov-read-b* (fn-own-read *ov-reader-b* 2 *ov-hdr*))
(assert-event
 (equal (fn-served-reply-octets (car *ov-read-a*))
        (append (fn-nntp-string-octets
                 "430 no article with that message-id") '(13 10))))
(assert-event
 (equal (fn-served-reply-octets (car *ov-read-b*))
        (append (fn-nntp-string-octets "225 headers follow")
                '(13 10 48 32)
                (fn-nntp-string-octets "verified ")
                (fn-stx-hex-octets *sit-principal*)
                (fn-nntp-string-octets " keyring 1")
                '(13 10 46 13 10))))
(assert-event (not (equal (car *ov-read-a*) (car *ov-read-b*))))

; A later durable keyring generation changes current authority, not the
; verdict the earlier reader pinned or the value a new reader sees for the
; older accepted article.
(defconst *ov-new-keys*
  (list (cons :ed25519 (make-list 32 :initial-element 23))
        (cons :ml-dsa-65 (make-list 1952 :initial-element 29))))
(make-event `(defconst *ov-second-enrollment*
               ',(fn-hsig-keyring-event 2 2 2 2 *sit-principal* *ov-new-keys*)))
(assert-event (fn-stxk-p *ov-second-enrollment*))
(assert-event (equal (fn-sn-identity-next (fn-own-store *ov-reader-b*)) 2))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store
                                                (fn-own-step *ov-reader-b*
                                                             '(:begin 1)))))
                     :ready))
(assert-event
 (equal (fn-stxk-context-kind
         (fn-replay-identity-step
          (fn-sn-identity-context (fn-own-store *ov-reader-b*))
          *ov-second-enrollment*))
        :ok))
(defconst *ov-rotation-events*
  (list '(:store (:io :start-frontier nil))
        '(:store (:io :frontier-file :ok))
        '(:store (:io :frontier-replace :ok))
        '(:store (:io :frontier-directory :ok))
        (list :store (list :prepare-identity *ov-second-enrollment*))
        '(:store (:io :record-file :ok))
        '(:store (:io :record-link :ok))
        '(:store (:io :record-directory :ok))
        '(:complete)))
(make-event `(defconst *ov-rotated*
               ',(fn-own-run (fn-own-step *ov-reader-b* '(:begin 1))
                             *ov-rotation-events*)))
(assert-event (equal (fn-stxk-keyring-generation
                      (car (fn-sn-keyring-snapshots (fn-own-store *ov-rotated*))))
                     2))
(assert-event
 (equal (fn-own-conn-verdicts
         (fn-own-find-conn 2 (fn-own-conns *ov-rotated*)))
        (fn-own-conn-verdicts
         (fn-own-find-conn 2 (fn-own-conns *ov-reader-b*)))))
(defconst *ov-read-b-after-rotation*
  (fn-own-read *ov-rotated* 2 *ov-hdr*))
(assert-event
 (equal (fn-served-reply-octets (car *ov-read-b-after-rotation*))
        (fn-served-reply-octets (car *ov-read-b*))))
(defconst *ov-reader-c* (cdr (fn-own-open *ov-rotated* nil)))
(assert-event
 (equal (fn-served-reply-octets
         (car (fn-own-read *ov-reader-c* 3 *ov-hdr*)))
        (fn-served-reply-octets (car *ov-read-b*))))

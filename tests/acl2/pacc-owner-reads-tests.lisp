; PACC ground witnesses and historical single-triple audit, test-only.
(in-package "ACL2")

(include-book "../../books/pacc-chain")
(include-book "../../books/poster-bytes-invariants")

(defun fn-pacc-single-local-sub-readp (sub secret take-config parse-carry read-limits)
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-own-sub-decision sub)))
    (implies (and (equal (fn-own-sub-source-context sub) :post-d25)
                  (fn-inj-injectedp d)
                  (not (fn-peer-submissionp d)))
             (fn-pacc-sub-readp sub secret take-config parse-carry read-limits))))

(defun fn-pacc-single-queue-readp (queue secret take-config parse-carry read-limits)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp queue)
      (and (fn-pacc-single-local-sub-readp (fn-psub-unpack-sub (car queue))
                                    secret take-config parse-carry read-limits)
           (fn-pacc-single-queue-readp (cdr queue) secret take-config parse-carry read-limits))
    t))

(defun fn-pacc-conns-carry-profile-headersp (conns profile)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp conns)
      (and (equal (fn-inj-config-header-limits (fn-own-conn-config (car conns)))
                  (fn-bs-profile-header-limits profile))
           (fn-pacc-conns-carry-profile-headersp (cdr conns) profile))
    t))

(defun fn-pacc-pins-carry-profile-headersp (o profile)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-inj-config-header-limits (fn-own-config o))
              (fn-bs-profile-header-limits profile))
       (fn-pacc-conns-carry-profile-headersp (fn-own-conns o) profile)))

(defun fn-pacc-single-owner-readsp (state)
  (declare (xargs :stobjs state :guard t :verify-guards nil))
  (let* ((o (fn-ocfg-owner (fn-owner-ocfg state)))
         (profile (fn-owner-store-profile state))
         (h (fn-bs-profile-header-limits profile)))
    (and (fn-pacc-pins-carry-profile-headersp o profile)
         (fn-pacc-single-queue-readp (fn-own-queue o) nil nil nil h)
         (fn-pacc-single-local-sub-readp (fn-own-inflight o) nil nil nil h))))

(defun fn-pacc-v3-owner-value-readsp (o current-profile) (declare (xargs :guard t :verify-guards nil)) (let ((h (fn-bs-profile-header-limits current-profile))) (and (fn-pacc-pins-read-own-headersp o) (fn-pacc-single-queue-readp (fn-own-queue o) nil nil nil h) (fn-pacc-single-local-sub-readp (fn-own-inflight o) nil nil nil h))))

(local (defthm fn-pacc-queue-readp-append-l
 (equal (fn-pacc-single-queue-readp (append q (list packed)) secret cfg carry h)
  (and (fn-pacc-single-queue-readp q secret cfg carry h)
       (fn-pacc-single-local-sub-readp (fn-psub-unpack-sub packed) secret cfg carry h)))
 :hints (("Goal" :induct (fn-pacc-single-queue-readp q secret cfg carry h)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-single-queue-readp binary-append car-cons cdr-cons (:type-prescription fn-pacc-single-local-sub-readp) (:type-prescription fn-pacc-single-queue-readp)))))))

(defthm fn-pacc-enqueue-carries-sub-readp-at-item-triple
  (implies
   (and (fn-pacc-sub-readp sub secret take-config parse-carry read-limits)       ; EQ1
        (fn-pacc-single-queue-readp (fn-own-queue o) secret take-config
                             parse-carry read-limits))                           ; EQ2
   (fn-pacc-single-queue-readp (fn-own-queue (fn-own-enqueue o sub))
                        secret take-config parse-carry read-limits))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-own-enqueue fn-own-queue fn-own-make fn-ag-append fn-pacc-queue-readp-append-l
 fn-pacc-single-local-sub-readp fn-psub-unpack-of-pack-sub car-cons cdr-cons)))))

(defthm fn-pacc-single-profile-install-core-establishes-pins-when-unconnected
  (implies (and (fn-bs-profile-admittedp profile)
                (not (consp (fn-own-conns o))))
           (fn-pacc-pins-carry-profile-headersp (mv-nth 1 (fn-osb-install o profile)) profile))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-osb-install-serves-the-profile-header-limits)) :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-pins-carry-profile-headersp fn-pacc-conns-carry-profile-headersp fn-osb-install-serves-the-profile-header-limits fn-osb-install fn-own-configure fn-own-conns-of-fn-own-make mv-nth nfix zp car-cons cdr-cons (:executable-counterpart consp))))))

(defthm fn-pacc-single-startup-install-establishes-owner-reads
  (let* ((oc (fn-ock-install replayed opened max-conns))
         (o2 (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile)))
         (h (fn-bs-profile-header-limits profile)))
    (implies (and (not (equal oc :fault))
                  (fn-bs-profile-admittedp profile))
             (and (fn-pacc-pins-carry-profile-headersp o2 profile)
                  (fn-pacc-single-queue-readp (fn-own-queue o2) nil nil nil h)
                  (fn-pacc-single-local-sub-readp (fn-own-inflight o2) nil nil nil h))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-pacc-recovered-owner-has-no-local-work)) :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-single-profile-install-core-establishes-pins-when-unconnected fn-pacc-recovered-owner-has-no-connections fn-pacc-recovered-owner-has-no-local-work fn-pacc-osb-install-keeps-queue-and-inflight fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp fn-own-sub-decision fn-own-sub-source-context fn-inj-injectedp fn-inj-decision-status fn-inj-nth fn-inj-car fn-inj-cdr fn-ag-car fn-ag-cdr nfix zp (:executable-counterpart consp) (:executable-counterpart equal))))))

(defthm fn-pacc-local-sub-readp-from-decision-readp
 (implies (and (fn-pacc-decision-readp (fn-own-sub-decision sub) h)
               (fn-own-sub-shapep sub) (fn-apc-p carry))
          (fn-pacc-single-local-sub-readp sub secret cfg carry h))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-successful-read-body (art (mv-nth 0 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (icfg (mv-nth 1 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (iclock (mv-nth 2 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (take-config cfg) (parse-carry carry))
       (:instance fn-pacc-read-body-establishes-readp (art (mv-nth 0 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (icfg (mv-nth 1 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (iclock (mv-nth 2 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (take-config cfg) (parse-carry carry) (read-limits h)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-decision-readp fn-pacc-single-local-sub-readp fn-pacc-sub-readp fn-pacc-sub-read-bodyp
 fn-own-sub-decision-of-fn-own-sub-make-author)))))

(defthm fn-pacc-enqueue-carries-local-sub-readp
 (implies (and (fn-pacc-single-local-sub-readp sub secret cfg carry h)
               (fn-pacc-single-queue-readp (fn-own-queue o) secret cfg carry h))
          (fn-pacc-single-queue-readp (fn-own-queue (fn-own-enqueue o sub)) secret cfg carry h))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-own-enqueue fn-own-queue fn-own-make fn-ag-append fn-pacc-queue-readp-append-l
 fn-psub-unpack-of-pack-sub car-cons cdr-cons)))))

(defthm fn-pacc-scar-finish-read-carries-queue-readp
 (implies (and (fn-pacc-single-queue-readp (fn-own-queue o) secret cfg carry h)
               (fn-pacc-effects-readp (fn-served-result-effects result) h)
               (fn-apc-p carry))
          (fn-pacc-single-queue-readp (fn-own-queue (cdr (fn-scar-finish-read o conn result live))) secret cfg carry h))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-scar-finish-read fn-own-set-conns fn-own-queue-of-fn-own-make
 fn-pacc-selected-submission-has-readp fn-pacc-local-sub-readp-from-decision-readp
 fn-own-sub-shapep-of-fn-own-sub-make-author fn-own-sub-decision-of-fn-own-sub-make-author
 fn-pacc-enqueue-carries-local-sub-readp cdr-cons)))))

(defthm fn-pacc-available-read-carries-queue-readp-at-item-triple
  (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
         (r (fn-av-scr-own-read-span o id i end cache
                                    fn-octets fn-arena fn-cat)))
    (implies
     (and (fn-octets-p fn-octets) (fn-arena-p fn-arena) (fn-cat-p fn-cat)       ; ER1-3 (a)
          (natp i) (natp end)                                                  ; ER4 (a) part
          (fn-apc-p parse-carry)                                               ; ER6 (a)
          (fn-pacc-single-queue-readp (fn-own-queue o) secret take-config
                               parse-carry read-limits)                        ; ER7 TOOTH-SHAPE
          (implies conn
                   (equal (fn-inj-config-header-limits (fn-own-conn-config conn))
                          read-limits)))                                       ; ER8 TOOTH-GATED
     (fn-pacc-single-queue-readp (fn-own-queue (fn-own-tls-result-owner r))
                          secret take-config parse-carry read-limits)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-own-read-span fn-own-tls-result-owner fn-own-tls-make-result
 fn-pacc-scar-finish-read-carries-queue-readp fn-pacc-av-step-fast-carries-read-effects-and-headers
 fn-pacc-own-tls-served-conn-keeps-header-limits fn-ag-car fn-ag-cdr
 car-cons cdr-cons (:executable-counterpart consp))))))

(defthm fn-pacc-replace-conn-keeps-headers
 (implies (and (fn-pacc-conns-carry-profile-headersp conns profile)
               (equal (fn-inj-config-header-limits (fn-own-conn-config conn)) (fn-bs-profile-header-limits profile)))
          (fn-pacc-conns-carry-profile-headersp (fn-own-replace-conn conn conns) profile))
 :hints (("Goal" :induct (fn-own-replace-conn conn conns)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-own-replace-conn fn-pacc-conns-carry-profile-headersp car-cons cdr-cons)))))

(defthm fn-pacc-remove-conn-keeps-headers
 (implies (fn-pacc-conns-carry-profile-headersp conns profile)
          (fn-pacc-conns-carry-profile-headersp (fn-own-remove-conn id conns) profile))
 :hints (("Goal" :induct (fn-own-remove-conn id conns)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-own-remove-conn fn-pacc-conns-carry-profile-headersp car-cons cdr-cons)))))

(defthm fn-pacc-found-conn-has-profile-headers
 (implies (and (fn-pacc-conns-carry-profile-headersp conns profile) (fn-own-find-conn id conns))
          (equal (fn-inj-config-header-limits (fn-own-conn-config (fn-own-find-conn id conns)))
                 (fn-bs-profile-header-limits profile)))
 :hints (("Goal" :induct (fn-own-find-conn id conns)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-own-find-conn fn-pacc-conns-carry-profile-headersp car-cons cdr-cons)))))

(defun a24p-lines (lines)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp lines) (append (fn-record-string-octets (car lines)) '(13 10) (a24p-lines (cdr lines))) nil))

(defun a24p-body (group mid)
 (declare (xargs :guard t :verify-guards nil))
 (list (fn-record-string-octets "From: poster@example.invalid")
       (fn-record-string-octets "Subject: hello")
       (fn-record-string-octets (concatenate 'string "Newsgroups: " group))
       (fn-record-string-octets (concatenate 'string "Message-ID: " mid))
       nil (fn-record-string-octets "Hello.")))

(defconst *a24p-clock* (fn-clock-observation 1000000 843004800000 500 t))

(defconst *a24p-profile* *fn-bs-profile-development*)

(defconst *a24p-h* (fn-bs-profile-header-limits *a24p-profile*))

(defconst *a24p-groups* '("fn.test" "fn.mod" "fn.queue"))

(defconst *a24p-entry*
 (list :moderated (fn-record-string-octets "fn.mod") (fn-record-string-octets "fn.queue")
       (list (fn-record-string-octets "alice"))))

(defconst *a24p-icfg*
 (fn-inj-make-config-full t (fn-record-string-octets "fn.example.invalid")
  (list (fn-record-string-octets "fn.test") (fn-record-string-octets "fn.mod")
        (fn-record-string-octets "fn.queue"))
  (fn-inj-post-bound 32768 *a24p-h*) nil (list *a24p-entry*)))

(defconst *a24p-store* (fn-sn-initial *a24p-groups* 100))

(defconst *a24p-owner* (fn-own-observe (fn-own-configure (fn-own-start *a24p-store* 4) *a24p-icfg*) *a24p-clock*))

(defconst *a24p-opened* (cdr (fn-own-open (cdr (fn-own-open *a24p-owner* nil)) nil)))

(defconst *a24p-archive* (fn-own-view-archive (fn-own-view *a24p-owner*)))

(defconst *a24p-ps* (fn-post-make-session (fn-nntp-open-session *a24p-archive*) t))

(defun a24p-produced-sub (body id)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (sub fn-arena)
   (let ((r (fn-nntp-post-step *a24p-ps* *a24p-archive* *a24p-icfg* *a24p-clock*
                    *a24p-clock* (list :article body) fn-arena)))
    (mv (fn-own-sub-make-author id 0 nil (fn-post-result-submission r) nil nil
              (fn-own-served-source-context (fn-post-result-submission r))) fn-arena))
   sub)))

(defconst *a24p-body-ordinary* (a24p-body "fn.test" "<ordinary@example.invalid>"))

(defconst *a24p-art-ordinary* (fn-post-body-octets *a24p-body-ordinary*))

(defconst *a24p-d-ordinary* (fn-post-gated-decision *a24p-art-ordinary* *a24p-icfg* *a24p-clock*))

(with-guard-checking-event :none
 (make-event
  (let ((sub (a24p-produced-sub *a24p-body-ordinary* 0)))
   (value (list 'defconst '*a24p-sub-ordinary* (list 'quote sub))))))

(with-guard-checking-event :none
 (assert-event
  (and (fn-mod-entry-well-formedp *a24p-entry*)
       (fn-inj-configp *a24p-icfg*) (fn-clock-observationp *a24p-clock*)
       (fn-inj-injectedp *a24p-d-ordinary*)
       (equal (fn-own-sub-decision *a24p-sub-ordinary*) *a24p-d-ordinary*)
       (fn-pacc-sub-read-bodyp *a24p-sub-ordinary* nil nil nil *a24p-h*
                         *a24p-art-ordinary* *a24p-icfg* *a24p-clock*)
       (fn-pacc-injectionp (fn-pacc-sub-inj *a24p-sub-ordinary* nil nil nil *a24p-icfg* *a24p-clock*)
                          *a24p-art-ordinary*))))

(cw "~%A24-ORDINARY-READ-BODY ~x0~%"
 (fn-pacc-sub-read-bodyp *a24p-sub-ordinary* nil nil nil *a24p-h*
                         *a24p-art-ordinary* *a24p-icfg* *a24p-clock*))

(defconst *a24p-body-moderated* (a24p-body "fn.mod" "<moderated@example.invalid>"))

(defconst *a24p-art-moderated* (fn-post-body-octets *a24p-body-moderated*))

(defconst *a24p-d-moderated* (fn-post-gated-decision *a24p-art-moderated* *a24p-icfg* *a24p-clock*))

(with-guard-checking-event :none
 (make-event
  (let ((sub (a24p-produced-sub *a24p-body-moderated* 1)))
   (value (list 'defconst '*a24p-sub-moderated* (list 'quote sub))))))

(with-guard-checking-event :none
 (assert-event
  (and (fn-mod-entry-well-formedp *a24p-entry*)
       (fn-inj-configp *a24p-icfg*) (fn-clock-observationp *a24p-clock*)
       (fn-inj-injectedp *a24p-d-moderated*)
       (equal (fn-own-sub-decision *a24p-sub-moderated*) *a24p-d-moderated*)
       (fn-pacc-sub-read-bodyp *a24p-sub-moderated* nil nil nil *a24p-h*
                         *a24p-art-moderated* *a24p-icfg* *a24p-clock*)
       (fn-pacc-injectionp (fn-pacc-sub-inj *a24p-sub-moderated* nil nil nil *a24p-icfg* *a24p-clock*)
                          *a24p-art-moderated*))))

(cw "~%A24-MODERATED-READ-BODY ~x0~%"
 (fn-pacc-sub-read-bodyp *a24p-sub-moderated* nil nil nil *a24p-h*
                         *a24p-art-moderated* *a24p-icfg* *a24p-clock*))

(cw "~%A24-MODERATED-TARGET ~x0~%" (list (fn-inj-decision-groups *a24p-d-moderated*) (fn-inj-decision-msgid *a24p-d-moderated*)))

(cw "~%A24-ILLEGAL-AFTER-FIXTURES ~x0~%" (@ illegal-to-certify-message))

(defthm fn-pacc-ordinary-fixture-has-whole-read-witness
 (and (fn-pacc-sub-read-bodyp *a24p-sub-ordinary* nil nil nil *a24p-h* *a24p-art-ordinary* *a24p-icfg* *a24p-clock*)
      (fn-pacc-sub-readp *a24p-sub-ordinary* nil nil nil *a24p-h*))
 :hints (("Goal" :use ((:instance fn-pacc-read-body-establishes-readp
                       (sub *a24p-sub-ordinary*) (secret nil) (take-config nil) (parse-carry nil)
                       (read-limits *a24p-h*) (art *a24p-art-ordinary*) (icfg *a24p-icfg*) (iclock *a24p-clock*)))
 :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-pacc-sub-read-bodyp))))))

(defthm fn-pacc-moderated-fixture-has-whole-read-witness
 (and (fn-pacc-sub-read-bodyp *a24p-sub-moderated* nil nil nil *a24p-h* *a24p-art-moderated* *a24p-icfg* *a24p-clock*)
      (fn-pacc-sub-readp *a24p-sub-moderated* nil nil nil *a24p-h*))
 :hints (("Goal" :use ((:instance fn-pacc-read-body-establishes-readp
                       (sub *a24p-sub-moderated*) (secret nil) (take-config nil) (parse-carry nil)
                       (read-limits *a24p-h*) (art *a24p-art-moderated*) (icfg *a24p-icfg*) (iclock *a24p-clock*)))
 :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-pacc-sub-read-bodyp))))))

(defconst *a25-pacc-shape-phantom* (append *a24p-sub-ordinary* '(extra)))

(with-guard-checking-event :none
 (assert-event (and (not (fn-own-sub-shapep *a25-pacc-shape-phantom*))
                    (fn-inj-injectedp (fn-own-sub-decision *a25-pacc-shape-phantom*))
                    (equal (fn-own-sub-source-context *a25-pacc-shape-phantom*) :post-d25)
                    (not (fn-peer-submissionp (fn-own-sub-decision *a25-pacc-shape-phantom*))))))

(defthm fn-pacc-shape-phantom-has-no-read-witness
 (not (fn-pacc-sub-readp *a25-pacc-shape-phantom* nil nil nil *a24p-h*))
 :hints (("Goal" :use ((:instance fn-pacc-sub-readp-fixes-shape
                       (sub *a25-pacc-shape-phantom*) (secret nil) (take-config nil) (parse-carry nil) (read-limits *a24p-h*)))
 :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-own-sub-shapep))))))

(with-guard-checking-event :none
 (assert-event (and (not (fn-pacc-gated-header-roomp *a24p-d-ordinary* '(1 1 1)))
                    (not (fn-pacc-gated-header-roomp *a24p-d-moderated* '(1 1 1))))))

(defthm fn-pacc-ordinary-bad-header-room-has-no-read-witness
 (not (fn-pacc-sub-readp *a24p-sub-ordinary* nil nil nil '(1 1 1)))
 :hints (("Goal" :use ((:instance fn-pacc-sub-readp-fixes-gated-header-room
                       (sub *a24p-sub-ordinary*) (secret nil) (take-config nil) (parse-carry nil) (read-limits '(1 1 1))))
 :in-theory (union-theories (theory 'minimal-theory)
 '((:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-pacc-gated-header-roomp))))))

(defthm fn-pacc-moderated-bad-header-room-has-no-read-witness
 (not (fn-pacc-sub-readp *a24p-sub-moderated* nil nil nil '(1 1 1)))
 :hints (("Goal" :use ((:instance fn-pacc-sub-readp-fixes-gated-header-room
                       (sub *a24p-sub-moderated*) (secret nil) (take-config nil) (parse-carry nil) (read-limits '(1 1 1))))
 :in-theory (union-theories (theory 'minimal-theory)
 '((:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-pacc-gated-header-roomp))))))

(defconst *a25-limit-profile* *fn-bs-profile-development*)

(defconst *a25-limit-changed-profile*
 (fn-lim-set-nth *fn-bs-pf-max-header-fields* 10 *a25-limit-profile*))

(defconst *a25-limit-recovered*
 (let ((configs (list *fn-cfg-default-record*)))
  (fn-ock-recover-extended (fn-sco-extend (fn-sco-capture configs nil) configs nil)
                          configs 0 4)))

(defconst *a25-limit-installed*
 (mv-let (verdict owner) (fn-osb-install (fn-ocfg-owner *a25-limit-recovered*) *a25-limit-profile*)
  (declare (ignore verdict)) (fn-ocfg-with-owner *a25-limit-recovered* owner)))

(defconst *a25-limit-opened* (cdr (fn-ocar-ocfg-open *a25-limit-installed* nil)))

(defconst *a25-limit-after-owner*
 (mv-let (verdict owner) (fn-osb-install (fn-ocfg-owner *a25-limit-opened*) *a25-limit-changed-profile*)
  (declare (ignore verdict)) owner))

(with-guard-checking-event :none
 (assert-event
  (and (not (equal *a25-limit-recovered* :fault))
       (fn-bs-profile-admittedp *a25-limit-profile*)
       (fn-bs-profile-admittedp *a25-limit-changed-profile*)
       (fn-lgoc-invariantp *a25-limit-opened*)
       (consp (fn-own-conns (fn-ocfg-owner *a25-limit-opened*)))
       (fn-pacc-pins-carry-profile-headersp (fn-ocfg-owner *a25-limit-opened*) *a25-limit-profile*)
       (not (consp (fn-own-queue (fn-ocfg-owner *a25-limit-opened*))))
       (null (fn-own-inflight (fn-ocfg-owner *a25-limit-opened*)))
       (not (fn-pacc-pins-carry-profile-headersp *a25-limit-after-owner* *a25-limit-changed-profile*)))))

(cw "~%A25-LIMIT-CONTROL ~x0~%"
 (list (fn-bs-profile-admittedp *a25-limit-changed-profile*)
       (fn-lgoc-invariantp *a25-limit-opened*)
       (fn-pacc-pins-carry-profile-headersp (fn-ocfg-owner *a25-limit-opened*) *a25-limit-profile*)
       (fn-bs-profile-header-limits *a25-limit-profile*)
       (fn-bs-profile-header-limits *a25-limit-changed-profile*)
       (fn-inj-config-header-limits (fn-own-conn-config (car (fn-own-conns *a25-limit-after-owner*))))
       (fn-pacc-pins-carry-profile-headersp *a25-limit-after-owner* *a25-limit-changed-profile*)))

(defthm fn-pacc-limit-counterexample-before-has-owner-reads
 (implies (and (equal (fn-owner-ocfg state) *a25-limit-opened*)
               (equal (fn-owner-store-profile state) *a25-limit-profile*))
          (fn-pacc-single-owner-readsp state))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-single-owner-readsp fn-ocfg-owner fn-own-queue fn-own-inflight
 fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp fn-own-sub-source-context fn-own-sub-decision
 fn-ag-car fn-ag-cdr car-cons cdr-cons
 (:executable-counterpart fn-pacc-pins-carry-profile-headersp)
 (:executable-counterpart fn-bs-profile-header-limits)
 (:executable-counterpart consp) (:executable-counterpart equal)
 (:executable-counterpart car) (:executable-counterpart cdr))))))

(defthm fn-pacc-limit-counterexample-after-has-no-owner-reads
 (implies (and (equal (fn-owner-core state) *a25-limit-after-owner*)
               (equal (fn-owner-store-profile state) *a25-limit-changed-profile*))
          (not (fn-pacc-single-owner-readsp state)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-single-owner-readsp fn-owner-core-is-configured-owner-by-definition
 (:executable-counterpart fn-pacc-pins-carry-profile-headersp))))))

(defun fn-pacc-limit-counterexample-seed (state)
 (declare (xargs :stobjs state :guard t :verify-guards nil))
 (let* ((state (fn-owner-install-ocfg *a25-limit-opened* state))
        (state (f-put-global 'fn-owner-store-profile *a25-limit-profile* state))
        (state (f-put-global 'fn-owner-retain-carry nil state))
        (state (f-put-global 'fn-owner-canonical-admission-pending nil state))
        (state (f-put-global 'fn-owner-history-publication nil state))
        (state (f-put-global 'fn-owner-limit-carry (cons *a25-limit-profile* *a25-limit-profile*) state)))
  state))

(with-guard-checking-event :none
 (make-event
  (let* ((state (fn-pacc-limit-counterexample-seed state))
         (before
          (list (boundp-global 'fn-owner state)
                (fn-owner-history-bootstrap-mutationp state)
                (equal (fn-owner-ocfg state) *a25-limit-opened*)
                (equal (fn-owner-store-profile state) *a25-limit-profile*)
                (fn-owner-retain-statep state)
                (fn-prc-carryp (fn-owner-retain-carry state))
                (fn-bs-profile-admittedp *a25-limit-changed-profile*))))
   (mv-let (erp verdict state) (fn-owner-apply-limit-profile *a25-limit-changed-profile* state)
    (let ((after
           (list erp verdict
                 (equal (fn-owner-core state) *a25-limit-after-owner*)
                 (equal (fn-owner-store-profile state) *a25-limit-changed-profile*)
                 (fn-owner-retain-statep state)
                 (fn-prc-carryp (fn-owner-retain-carry state))
                 (fn-pacc-pins-carry-profile-headersp (fn-owner-core state) (fn-owner-store-profile state)))))
     (pprogn
      (fms "~%A25-HOST-LIMIT BEFORE ~x0 AFTER ~x1~%" (list (cons #\0 before) (cons #\1 after)) (standard-co state) state nil)
      (value (list 'assert-event
                   (list 'equal (list 'quote (list before after))
                         (list 'quote '((t t t t t t t) (nil :installed t t t t nil))))))))))))

(cw "~%A25-LIMIT-ILLEGAL ~x0~%" (@ illegal-to-certify-message))

(assert-event (equal (@ illegal-to-certify-message) nil))

; Approved ground teeth, including the quantified OLD-negative proof.
(defconst *v4-many-body* (append (take 4 *a24p-body-ordinary*) (list (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value") (fn-record-string-octets "X-Extra: value")) (nthcdr 4 *a24p-body-ordinary*)))

(defconst *v4-many-art* (fn-post-body-octets *v4-many-body*))

(with-guard-checking-event :none (make-event (value (list 'defconst '*v4-many-sub* (list 'quote (a24p-produced-sub *v4-many-body* 0))))))

(defconst *v4-before* (fn-own-enqueue (fn-ocfg-owner *a25-limit-opened*) *v4-many-sub*))

(defconst *v4-after* (mv-let (verdict after) (fn-osb-install *v4-before* *a25-limit-changed-profile*) (declare (ignore verdict)) after))

(defconst *v4-bad-sub* (append *v4-many-sub* '(extra)))

(defthm fn-pacc-many-fixture-has-whole-read-witness
 (and (fn-pacc-sub-readp *v4-many-sub* nil nil nil '(64 256 16384))
      (fn-pacc-sub-read-at-profilep *v4-many-sub* nil nil nil *a25-limit-profile*)
      (fn-pacc-item-sub-readp *v4-many-sub* nil nil nil))
 :hints (("Goal" :use ((:instance fn-pacc-read-body-establishes-readp
 (sub *v4-many-sub*) (secret nil) (take-config nil) (parse-carry nil)
 (read-limits '(64 256 16384)) (art *v4-many-art*) (icfg *a24p-icfg*) (iclock *a24p-clock*))
 (:instance fn-pacc-profile-witness-establishes-item-read (sub *v4-many-sub*)
 (secret nil) (cfg nil) (carry nil) (profile *a25-limit-profile*)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-sub-read-at-profilep (:executable-counterpart fn-bs-profile-header-limits)
 (:executable-counterpart fn-bs-profile-admittedp) (:executable-counterpart fn-pacc-sub-read-bodyp))))))

(local (defthm fn-pacc-test-injection-census
 (implies (fn-inj-injectedp (fn-inj-decide source config obs))
 (not (fn-article-census-refusal (fn-article-header-census source) (fn-inj-config-header-limits config))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-inj-decide fn-inj-injectedp fn-inj-refuse fn-inj-decision-status-of-fn-inj-make-decision))))))

(local (defthm fn-pacc-envelope-never-has-many-fixture-msgid
 (not (equal (fn-mod-envelope-msgid m) (fn-inj-decision-msgid (fn-own-sub-decision *v4-many-sub*))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-mod-envelope-msgid fn-inj-append car-cons cdr-cons
 (:executable-counterpart fn-inj-decision-msgid) (:executable-counterpart fn-own-sub-decision)
 (:executable-counterpart equal) (:executable-counterpart consp)))))))

(local (defthm fn-pacc-gated-many-fixture-is-direct-injection
 (implies (equal (fn-post-gated-decision art icfg iclock) (fn-own-sub-decision *v4-many-sub*))
 (equal (fn-inj-decide art icfg iclock) (fn-own-sub-decision *v4-many-sub*)))
 :hints (("Goal" :use ((:instance fn-post-gated-decision-is-the-decision-or-its-envelope
 (source art) (config icfg) (injection iclock)) (:instance fn-pacc-envelope-never-has-many-fixture-msgid (m (fn-inj-decision-msgid (fn-inj-decide art icfg iclock)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '((:executable-counterpart fn-inj-decision-msgid)
 (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-own-sub-decision)))))))

(local (defthm fn-pacc-direct-many-fixture-fixes-source
 (implies (equal (fn-inj-decide art icfg iclock) (fn-own-sub-decision *v4-many-sub*))
 (equal art *v4-many-art*))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-inj-source-of-inverts-the-injection
 (source art) (config icfg) (observation iclock))
 (:instance fn-pb-path-agent-of-an-injection (source art) (config icfg) (obs iclock)))
 :in-theory (union-theories (theory 'minimal-theory)
 '((:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp)
 (:executable-counterpart fn-inj-decision-octets) (:executable-counterpart fn-inj-decision-msgid)
 (:executable-counterpart fn-pb-path-agent) (:executable-counterpart fn-inj-source-of)
 cons-equal))))))

(local (defthm fn-pacc-gated-many-fixture-cannot-have-ten-header-triple
 (implies (equal (fn-inj-config-header-limits icfg) '(10 256 16384))
 (not (equal (fn-post-gated-decision art icfg iclock) (fn-own-sub-decision *v4-many-sub*))))
 :hints (("Goal" :use (fn-pacc-gated-many-fixture-is-direct-injection
 fn-pacc-direct-many-fixture-fixes-source
 (:instance fn-pacc-test-injection-census (source art) (config icfg) (obs iclock)))
 :in-theory (union-theories (theory 'minimal-theory)
 '((:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp)
 (:executable-counterpart fn-article-header-census) (:executable-counterpart fn-article-census-refusal)))))))

(defthm fn-pacc-many-fixture-has-no-ten-header-read-witness
 (not (fn-pacc-sub-readp *v4-many-sub* secret cfg carry '(10 256 16384)))
 :hints (("Goal" :use ((:instance fn-pacc-gated-many-fixture-cannot-have-ten-header-triple
 (art (mv-nth 0 (fn-pacc-sub-readp-witness *v4-many-sub* secret cfg carry '(10 256 16384))))
 (icfg (mv-nth 1 (fn-pacc-sub-readp-witness *v4-many-sub* secret cfg carry '(10 256 16384))))
 (iclock (mv-nth 2 (fn-pacc-sub-readp-witness *v4-many-sub* secret cfg carry '(10 256 16384))))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-sub-readp fn-pacc-sub-read-bodyp)))))

(defthm fn-pacc-perconn-64-to-10-control (let ((before (fn-ocfg-owner *a25-limit-opened*))) (mv-let (verdict after) (fn-osb-install before *a25-limit-changed-profile*) (and (fn-bs-profile-admittedp *a25-limit-profile*) (fn-bs-profile-admittedp *a25-limit-changed-profile*) (consp (fn-own-conns before)) (equal (fn-bs-profile-header-limits *a25-limit-profile*) (quote (64 256 16384))) (equal (fn-bs-profile-header-limits *a25-limit-changed-profile*) (quote (10 256 16384))) (equal verdict :installed) (fn-pacc-pins-carry-profile-headersp before *a25-limit-profile*) (not (fn-pacc-pins-carry-profile-headersp after *a25-limit-changed-profile*)) (equal after *a25-limit-after-owner*) (equal (fn-own-conns after) (fn-own-conns before)) (equal (fn-inj-config-header-limits (fn-own-config after)) (quote (10 256 16384))) (equal (fn-inj-config-header-limits (fn-own-conn-config (car (fn-own-conns after)))) (quote (64 256 16384))) (fn-pacc-pins-read-own-headersp before) (fn-pacc-pins-read-own-headersp after))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-owner-value-readsp fn-pacc-v3-owner-value-readsp fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp fn-pacc-queue-readp fn-pacc-local-sub-readp fn-pacc-inflight-readp fn-pacc-every-owner-pin-reads-own-headers fn-pacc-many-fixture-has-whole-read-witness fn-pacc-many-fixture-has-no-ten-header-read-witness (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-osb-install) (:executable-counterpart fn-ocfg-owner) (:executable-counterpart fn-own-queue) (:executable-counterpart fn-own-inflight) (:executable-counterpart fn-psub-unpack-sub) (:executable-counterpart fn-own-sub-source-context) (:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-peer-submissionp) (:executable-counterpart fn-bs-profile-header-limits) (:executable-counterpart fn-bs-profile-admittedp) (:executable-counterpart fn-pacc-pins-carry-profile-headersp) (:executable-counterpart fn-own-conns) (:executable-counterpart fn-own-config) (:executable-counterpart fn-own-conn-config) (:executable-counterpart fn-inj-config-header-limits) (:executable-counterpart len) (:executable-counterpart consp) (:executable-counterpart equal) car-cons cdr-cons)))))

(defthm fn-pacc-peritem-64-to-10-positive (let ((before (fn-own-enqueue (fn-ocfg-owner *a25-limit-opened*) *v4-many-sub*))) (mv-let (verdict after) (fn-osb-install before *a25-limit-changed-profile*) (and (equal verdict :installed) (equal (fn-bs-profile-header-limits *a25-limit-profile*) (quote (64 256 16384))) (equal (fn-bs-profile-header-limits *a25-limit-changed-profile*) (quote (10 256 16384))) (equal (len (fn-own-queue before)) 1) (equal (fn-own-queue after) (fn-own-queue before)) (fn-pacc-owner-value-readsp before) (fn-pacc-owner-value-readsp after))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-owner-value-readsp fn-pacc-v3-owner-value-readsp fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp fn-pacc-queue-readp fn-pacc-local-sub-readp fn-pacc-inflight-readp fn-pacc-every-owner-pin-reads-own-headers fn-pacc-many-fixture-has-whole-read-witness fn-pacc-many-fixture-has-no-ten-header-read-witness (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-osb-install) (:executable-counterpart fn-ocfg-owner) (:executable-counterpart fn-own-queue) (:executable-counterpart fn-own-inflight) (:executable-counterpart fn-psub-unpack-sub) (:executable-counterpart fn-own-sub-source-context) (:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-peer-submissionp) (:executable-counterpart fn-bs-profile-header-limits) (:executable-counterpart fn-bs-profile-admittedp) (:executable-counterpart fn-pacc-pins-carry-profile-headersp) (:executable-counterpart fn-own-conns) (:executable-counterpart fn-own-config) (:executable-counterpart fn-own-conn-config) (:executable-counterpart fn-inj-config-header-limits) (:executable-counterpart len) (:executable-counterpart consp) (:executable-counterpart equal) car-cons cdr-cons)))))

(defthm fn-pacc-peritem-64-to-10-old-negative (let ((before (fn-own-enqueue (fn-ocfg-owner *a25-limit-opened*) *v4-many-sub*))) (mv-let (verdict after) (fn-osb-install before *a25-limit-changed-profile*) (and (equal verdict :installed) (fn-pacc-v3-owner-value-readsp before *a25-limit-profile*) (not (fn-pacc-v3-owner-value-readsp after *a25-limit-changed-profile*)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-owner-value-readsp fn-pacc-v3-owner-value-readsp fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp fn-pacc-queue-readp fn-pacc-local-sub-readp fn-pacc-inflight-readp fn-pacc-every-owner-pin-reads-own-headers fn-pacc-many-fixture-has-whole-read-witness fn-pacc-many-fixture-has-no-ten-header-read-witness (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-osb-install) (:executable-counterpart fn-ocfg-owner) (:executable-counterpart fn-own-queue) (:executable-counterpart fn-own-inflight) (:executable-counterpart fn-psub-unpack-sub) (:executable-counterpart fn-own-sub-source-context) (:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-peer-submissionp) (:executable-counterpart fn-bs-profile-header-limits) (:executable-counterpart fn-bs-profile-admittedp) (:executable-counterpart fn-pacc-pins-carry-profile-headersp) (:executable-counterpart fn-own-conns) (:executable-counterpart fn-own-config) (:executable-counterpart fn-own-conn-config) (:executable-counterpart fn-inj-config-header-limits) (:executable-counterpart len) (:executable-counterpart consp) (:executable-counterpart equal) car-cons cdr-cons)))))

; Approved ground body matrices.
(defun v4-read-body-at-profilep (sub art icfg iclock profile secret cfg carry)
 (declare (xargs :guard t :verify-guards nil))
 (and (fn-bs-profile-admittedp profile)
      (fn-pacc-sub-read-bodyp sub secret cfg carry (fn-bs-profile-header-limits profile) art icfg iclock)))

(defun v4-u-body-matrix (s sub art icfg read-limits profile boundary-domain fn-octets fn-cat)
 (declare (xargs :stobjs (fn-octets fn-cat) :guard t :verify-guards nil))
 (let* ((d (fn-own-sub-decision sub)) (pcarry (fn-pvc-make profile)) (carry (cdr (fn-apc-take nil sub nil)))
        (filing (fn-ars-filing-plan (fn-inj-decision-groups d) boundary-domain fn-octets))
        (codes (fn-store-codes-from-groups (fn-pacc-derived-names (fn-pctx-get 1 filing)) boundary-domain)))
 (list (fn-octets-p fn-octets) (fn-cat-p fn-cat) (fn-sn-statep s) (fn-pvc-carryp pcarry) (fn-apc-p carry)
       (fn-pacc-sub-read-bodyp sub nil nil carry read-limits art icfg *a24p-clock*)
       (equal (fn-octets-list fn-octets) (fn-own-sub-stored-octets nil sub nil))
       (equal read-limits (fn-bs-profile-header-limits profile))
       (equal boundary-domain (fn-state-groups (fn-node-acceptance (fn-sn-node s))))
       (equal (fn-ars-carrier-form fn-octets) :absent)
       (equal (fn-pak-post-admission pcarry profile (fn-inj-decision-msgid d) (fn-octets-len fn-octets)
                (len codes) (fn-charge-for-payload (fn-octets-len fn-octets)) (make-list 32 :initial-element 0) fn-cat) :ok)
       (fn-pacc-profile-admitted-postp s art (fn-pacc-sub-inj sub nil nil carry icfg *a24p-clock*) profile pcarry)
       (v4-read-body-at-profilep sub art icfg *a24p-clock* profile nil nil carry))))

(defun v4-er-body-matrix (sub fn-octets fn-arena fn-cat)
 (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :guard t :verify-guards nil))
 (let* ((o (fn-own-enqueue *a24p-owner* sub))
        (r (fn-av-scr-own-read-span o 99 0 0 nil fn-octets fn-arena fn-cat))
        (after (fn-own-tls-result-owner r)))
 (list (fn-octets-p fn-octets) (fn-arena-p fn-arena) (fn-cat-p fn-cat) (natp 0) (natp 0) (fn-apc-p nil)
       (v4-read-body-at-profilep (fn-psub-unpack-sub (car (fn-own-queue o))) *a24p-art-ordinary* *a24p-icfg* *a24p-clock* *a24p-profile* nil nil nil)
       (v4-read-body-at-profilep (fn-psub-unpack-sub (car (fn-own-queue after))) *a24p-art-ordinary* *a24p-icfg* *a24p-clock* *a24p-profile* nil nil nil)
       (fn-own-sub-shapep (fn-psub-unpack-sub (car (fn-own-queue after)))))))

(defun v4-take-body-matrix-fixed (staged fn-arena)
 (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
 (let* ((o (fn-own-enqueue *a24p-owner* *a24p-sub-ordinary*))
        (oc (fn-ocfg-make o nil nil staged)) (head (fn-psub-unpack-sub (car (fn-own-queue o))))
        (next (fn-ocfg-step oc (list :take) fn-arena)) (after (fn-ocfg-owner next))
        (sub (fn-own-inflight after)) (cfg (fn-ocfg-config next)) (secret (fn-own-node-secret after))
        (tk (fn-apc-take cfg sub secret)))
 (list (fn-arena-p fn-arena) (null (fn-ocfg-staged oc)) (null (fn-own-inflight o)) (consp (fn-own-queue o))
       (null (fn-own-pending o)) (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready)
       (v4-read-body-at-profilep head *a24p-art-ordinary* *a24p-icfg* *a24p-clock* *a24p-profile* secret cfg (cdr tk))
       (v4-read-body-at-profilep sub *a24p-art-ordinary* *a24p-icfg* *a24p-clock* *a24p-profile* secret cfg (cdr tk))
       (fn-apc-p (cdr tk)) (equal (car tk) (fn-own-sub-stored-octets cfg sub secret)))))

(defun v4-ground-u-case (bad-domain)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-octets
  (mv-let (answer fn-octets)
   (let ((fn-octets (fn-octets-from-list (fn-own-sub-stored-octets nil *a24p-sub-ordinary* nil) fn-octets)))
    (mv (with-local-stobj fn-cat
         (mv-let (answer fn-cat)
          (mv (v4-u-body-matrix (if bad-domain (fn-sn-initial nil 100) *a24p-store*)
                *a24p-sub-ordinary* *a24p-art-ordinary* *a24p-icfg* *a24p-h*
                *a24p-profile* *a24p-groups* fn-octets fn-cat) fn-cat)
          answer)) fn-octets))
   answer)))

(defun v4-ground-take-case (staged)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (answer fn-arena) (mv (v4-take-body-matrix-fixed staged fn-arena) fn-arena) answer)))

(defun v4-ground-er-case (bad-queue)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-octets
  (mv-let (answer fn-octets)
   (mv (with-local-stobj fn-arena
        (mv-let (answer fn-arena)
         (mv (with-local-stobj fn-cat
              (mv-let (answer fn-cat)
               (mv (v4-er-body-matrix (if bad-queue (append *a24p-sub-ordinary* '(extra)) *a24p-sub-ordinary*) fn-octets fn-arena fn-cat) fn-cat)
               answer)) fn-arena)
         answer)) fn-octets)
   answer)))

(with-guard-checking-event :none
 (defthm fn-pacc-ground-u-positive-body (equal (v4-ground-u-case nil) (quote (T T T T T T T T T T T T T)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart v4-ground-u-case))))))
)

(with-guard-checking-event :none
 (defthm fn-pacc-ground-u-remove-U7-body (equal (v4-ground-u-case t) (quote (T T T T T T T T NIL T T NIL T)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart v4-ground-u-case))))))
)

(with-guard-checking-event :none
 (defthm fn-pacc-ground-take-positive-body (equal (v4-ground-take-case nil) (quote (T T T T T T T T T T)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart v4-ground-take-case))))))
)

(with-guard-checking-event :none
 (defthm fn-pacc-ground-take-remove-T2-body (equal (v4-ground-take-case t) (quote (T NIL T T T T T NIL T T)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart v4-ground-take-case))))))
)

(with-guard-checking-event :none
 (defthm fn-pacc-ground-er-positive-body (equal (v4-ground-er-case nil) (quote (T T T T T T T T T)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart v4-ground-er-case))))))
)

(with-guard-checking-event :none
 (defthm fn-pacc-ground-er-remove-ER7-body (equal (v4-ground-er-case t) (quote (T T T T T T NIL NIL NIL)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart v4-ground-er-case))))))
)

; Whole antecedent/conclusion and removal witnesses: landing-ground-whole.lisp
(defthm fn-pacc-item-readp-fixes-submission-shape
 (implies (fn-pacc-item-sub-readp sub secret cfg carry) (fn-own-sub-shapep sub))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pacc-sub-readp-fixes-shape
 (take-config cfg) (parse-carry carry)
 (read-limits (fn-bs-profile-header-limits (fn-pacc-item-sub-readp-witness sub secret cfg carry)))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-item-sub-readp fn-pacc-sub-read-at-profilep)))))

(defthm fn-pacc-malformed-item-has-no-read-witness
 (not (fn-pacc-item-sub-readp *v4-bad-sub* secret cfg carry))
 :hints (("Goal" :use ((:instance fn-pacc-item-readp-fixes-submission-shape (sub *v4-bad-sub*)))
 :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-own-sub-shapep))))))

(defthm fn-pacc-nil-item-has-no-read-witness
 (not (fn-pacc-item-sub-readp nil secret cfg carry))
 :hints (("Goal" :use ((:instance fn-pacc-item-readp-fixes-submission-shape (sub nil)))
 :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-own-sub-shapep))))))

(defthm fn-pacc-ordinary-fixture-has-item-profile-witness
 (fn-pacc-item-sub-readp *a24p-sub-ordinary* nil nil nil)
 :hints (("Goal" :use ((:instance fn-pacc-sub-readp-has-admitted-item-profile
 (sub *a24p-sub-ordinary*) (secret nil) (cfg nil) (carry nil) (h *a24p-h*)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-ordinary-fixture-has-whole-read-witness)))))

(defthm fn-pacc-ground-pin-establishment-positive
 (and (fn-pacc-pin3-enqueue-read-premisep *v4-many-sub* nil nil nil *a25-limit-profile*
 (car (fn-own-conns (fn-ocfg-owner *a25-limit-opened*))) *v4-many-art* *a24p-icfg* *a24p-clock*)
 (fn-pacc-sub-readp *v4-many-sub* nil nil nil (fn-bs-profile-header-limits *a25-limit-profile*))
 (fn-pacc-sub-read-at-profilep *v4-many-sub* nil nil nil *a25-limit-profile*)
 (fn-pacc-item-sub-readp *v4-many-sub* nil nil nil))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-many-fixture-has-whole-read-witness
 (:executable-counterpart fn-pacc-pin3-enqueue-read-premisep) (:executable-counterpart fn-own-conns) (:executable-counterpart fn-ocfg-owner) (:executable-counterpart car) (:executable-counterpart fn-bs-profile-header-limits))))))

(defthm fn-pacc-ground-pin-establishment-remove-premise
 (and (not (fn-pacc-pin3-enqueue-read-premisep *v4-bad-sub* nil nil nil *a25-limit-profile*
 (car (fn-own-conns (fn-ocfg-owner *a25-limit-opened*))) *v4-many-art* *a24p-icfg* *a24p-clock*))
 (not (fn-pacc-item-sub-readp *v4-bad-sub* nil nil nil)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-malformed-item-has-no-read-witness (:executable-counterpart fn-pacc-pin3-enqueue-read-premisep) (:executable-counterpart fn-own-conns) (:executable-counterpart fn-ocfg-owner) (:executable-counterpart car))))))

(defthm fn-pacc-ground-eq-positive
 (and (fn-pacc-item-sub-readp *a24p-sub-ordinary* nil nil nil)
 (fn-pacc-queue-readp (fn-own-queue *v4-before*) nil nil nil)
 (fn-pacc-queue-readp (fn-own-queue (fn-own-enqueue *v4-before* *a24p-sub-ordinary*)) nil nil nil))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-ordinary-fixture-has-item-profile-witness fn-pacc-many-fixture-has-whole-read-witness
 fn-pacc-queue-readp fn-pacc-local-sub-readp (:executable-counterpart fn-own-queue)
 (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-psub-unpack-sub)
 (:executable-counterpart fn-own-sub-source-context) (:executable-counterpart fn-own-sub-decision)
 (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-peer-submissionp) car-cons cdr-cons)))))

(defthm fn-pacc-ground-eq-remove-item-read
 (and (not (fn-pacc-item-sub-readp *v4-bad-sub* nil nil nil))
 (fn-pacc-queue-readp (fn-own-queue *v4-before*) nil nil nil)
 (not (fn-pacc-queue-readp (fn-own-queue (fn-own-enqueue *v4-before* *v4-bad-sub*)) nil nil nil)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-malformed-item-has-no-read-witness fn-pacc-many-fixture-has-whole-read-witness
 fn-pacc-queue-readp fn-pacc-local-sub-readp (:executable-counterpart fn-own-queue)
 (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-psub-unpack-sub)
 (:executable-counterpart fn-own-sub-source-context) (:executable-counterpart fn-own-sub-decision)
 (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-peer-submissionp) car-cons cdr-cons)))))

(defthm fn-pacc-ground-rb-positive
 (let ((carry (cdr (fn-apc-take nil *a24p-sub-ordinary* nil))))
 (and (fn-pacc-item-sub-readp *a24p-sub-ordinary* nil nil nil)
 (fn-apc-p carry) (fn-pacc-item-sub-readp *a24p-sub-ordinary* nil nil carry)))
 :hints (("Goal" :use ((:instance fn-pacc-item-sub-readp-rebinds-take-inputs
 (sub *a24p-sub-ordinary*) (secret0 nil) (cfg0 nil) (carry0 nil)
 (secret1 nil) (cfg1 nil) (carry1 (cdr (fn-apc-take nil *a24p-sub-ordinary* nil)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-ordinary-fixture-has-item-profile-witness (:executable-counterpart fn-apc-take)
 (:executable-counterpart fn-apc-p) (:executable-counterpart cdr))))))

(defthm fn-pacc-ground-rb-remove-source-read
 (and (not (fn-pacc-item-sub-readp *v4-bad-sub* nil nil nil))
 (fn-apc-p nil) (not (fn-pacc-item-sub-readp *v4-bad-sub* nil nil nil)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-malformed-item-has-no-read-witness (:executable-counterpart fn-apc-p))))))

(defun fn-pacc-ground-take-output (staged)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-arena
 (mv-let (answer fn-arena)
 (let* ((o (fn-own-enqueue *a24p-owner* *a24p-sub-ordinary*))
 (oc (fn-ocfg-make o nil nil staged)) (next (fn-ocfg-step oc (list :take) fn-arena))
 (after (fn-ocfg-owner next)) (sub (fn-own-inflight after)) (cfg (fn-ocfg-config next))
 (secret (fn-own-node-secret after)) (tk (fn-apc-take cfg sub secret)))
 (mv (list sub cfg secret (cdr tk)) fn-arena)) answer)))

(defthm fn-pacc-ground-take-whole-positive
 (let* ((out (fn-pacc-ground-take-output nil)) (sub (nth 0 out))
 (cfg (nth 1 out)) (secret (nth 2 out)) (carry (nth 3 out)))
 (and (equal (v4-ground-take-case nil) '(t t t t t t t t t t))
 (fn-pacc-sub-readp *a24p-sub-ordinary* secret cfg carry *a24p-h*)
 (fn-pacc-item-sub-readp *a24p-sub-ordinary* secret cfg carry)
 (fn-pacc-sub-readp sub secret cfg carry *a24p-h*)
 (fn-pacc-item-sub-readp sub secret cfg carry)))
 :hints (("Goal" :use ((:instance fn-pacc-read-body-establishes-readp
 (sub (nth 0 (fn-pacc-ground-take-output nil))) (secret (nth 2 (fn-pacc-ground-take-output nil)))
 (take-config (nth 1 (fn-pacc-ground-take-output nil))) (parse-carry (nth 3 (fn-pacc-ground-take-output nil)))
 (read-limits *a24p-h*) (art *a24p-art-ordinary*) (icfg *a24p-icfg*) (iclock *a24p-clock*))
 (:instance fn-pacc-sub-readp-rebinds-take-inputs (sub *a24p-sub-ordinary*)
 (secret0 nil) (cfg0 nil) (carry0 nil) (read-limits *a24p-h*)
 (secret1 (nth 2 (fn-pacc-ground-take-output nil))) (cfg1 (nth 1 (fn-pacc-ground-take-output nil)))
 (carry1 (nth 3 (fn-pacc-ground-take-output nil)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-sub-readp-has-admitted-item-profile fn-pacc-ordinary-fixture-has-whole-read-witness
 (:executable-counterpart fn-pacc-ground-take-output) (:executable-counterpart fn-pacc-sub-read-bodyp)
 (:executable-counterpart fn-apc-p) (:executable-counterpart v4-ground-take-case)
 (:executable-counterpart nth))))))

(defthm fn-pacc-ground-take-remove-staged-empty
 (and (equal (v4-ground-take-case t) '(t nil t t t t t nil t t))
 (not (fn-pacc-item-sub-readp (nth 0 (fn-pacc-ground-take-output t))
 (nth 2 (fn-pacc-ground-take-output t)) (nth 1 (fn-pacc-ground-take-output t))
 (nth 3 (fn-pacc-ground-take-output t)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-nil-item-has-no-read-witness (:executable-counterpart v4-ground-take-case)
 (:executable-counterpart fn-pacc-ground-take-output) (:executable-counterpart nth))))))

; Whole antecedent/conclusion and removal witnesses: landing-ground-er-u.lisp
(defun fn-pacc-ground-er-output (sub)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-octets
 (mv-let (answer fn-octets)
 (mv (with-local-stobj fn-arena
 (mv-let (answer fn-arena)
 (mv (with-local-stobj fn-cat
 (mv-let (answer fn-cat)
 (mv (fn-own-tls-result-owner
 (fn-av-scr-own-read-span (fn-own-enqueue *a24p-owner* sub) 99 0 0 nil fn-octets fn-arena fn-cat)) fn-cat)
 answer)) fn-arena) answer)) fn-octets) answer)))

(defthm fn-pacc-ground-er-whole-positive
 (and (equal (v4-ground-er-case nil) '(t t t t t t t t t))
 (fn-pacc-queue-readp (fn-own-queue (fn-own-enqueue *a24p-owner* *a24p-sub-ordinary*)) nil nil nil)
 (fn-pacc-queue-readp (fn-own-queue (fn-pacc-ground-er-output *a24p-sub-ordinary*)) nil nil nil))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-ordinary-fixture-has-item-profile-witness fn-pacc-queue-readp fn-pacc-local-sub-readp
 (:executable-counterpart v4-ground-er-case) (:executable-counterpart fn-own-queue)
 (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-pacc-ground-er-output)
 (:executable-counterpart fn-psub-unpack-sub) (:executable-counterpart fn-own-sub-source-context)
 (:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp)
 (:executable-counterpart fn-peer-submissionp) car-cons cdr-cons)))))

(defthm fn-pacc-ground-er-remove-queue-read
 (and (equal (v4-ground-er-case t) '(t t t t t t nil nil nil))
 (not (fn-pacc-queue-readp (fn-own-queue (fn-own-enqueue *a24p-owner* *v4-bad-sub*)) nil nil nil))
 (not (fn-pacc-queue-readp (fn-own-queue (fn-pacc-ground-er-output *v4-bad-sub*)) nil nil nil)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-malformed-item-has-no-read-witness fn-pacc-queue-readp fn-pacc-local-sub-readp
 (:executable-counterpart v4-ground-er-case) (:executable-counterpart fn-own-queue)
 (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-pacc-ground-er-output)
 (:executable-counterpart fn-psub-unpack-sub) (:executable-counterpart fn-own-sub-source-context)
 (:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp)
 (:executable-counterpart fn-peer-submissionp) car-cons cdr-cons)))))

(defthm fn-pacc-admission-of-two-read-recipes-with-same-headers
 (implies (equal (fn-inj-config-header-limits icfg1) (fn-inj-config-header-limits icfg0))
 (equal (fn-pacc-profile-admitted-postp s art1 (fn-pacc-sub-inj sub secret cfg carry icfg1 iclock1) profile pcarry)
        (fn-pacc-profile-admitted-postp s art0 (fn-pacc-sub-inj sub secret cfg carry icfg0 iclock0) profile pcarry)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-profile-admitted-postp fn-pacc-derived-fields fn-pacc-stored-payload
 fn-pacc-sub-inj fn-pctx-get nfix zp car-cons cdr-cons)))))

(defthm fn-pacc-read-witness-has-supplied-header-triple
 (implies (fn-pacc-sub-readp sub secret cfg carry h)
 (equal (fn-inj-config-header-limits (mv-nth 1 (fn-pacc-sub-readp-witness sub secret cfg carry h))) h))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-sub-readp fn-pacc-sub-read-bodyp)))))

(defconst *fn-pacc-ground-ordinary-carry* (cdr (fn-apc-take nil *a24p-sub-ordinary* nil)))

(defthm fn-pacc-ground-u-whole-positive
 (and (equal (v4-ground-u-case nil) '(t t t t t t t t t t t t t))
 (fn-pacc-sub-readp *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)
 (fn-pacc-item-sub-readp *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry*)
 (fn-pacc-profile-admitted-postp *a24p-store* *a24p-art-ordinary*
 (fn-pacc-sub-inj *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-icfg* *a24p-clock*)
 *a24p-profile* (fn-pvc-make *a24p-profile*)))
 :hints (("Goal" :use ((:instance fn-pacc-sub-readp-rebinds-take-inputs
 (sub *a24p-sub-ordinary*) (secret0 nil) (cfg0 nil) (carry0 nil) (read-limits *a24p-h*)
 (secret1 nil) (cfg1 nil) (carry1 *fn-pacc-ground-ordinary-carry*)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-ordinary-fixture-has-whole-read-witness fn-pacc-sub-readp-has-admitted-item-profile
 (:executable-counterpart v4-ground-u-case) (:executable-counterpart fn-apc-p)
 (:executable-counterpart fn-pacc-profile-admitted-postp) (:executable-counterpart fn-pacc-sub-inj)
 (:executable-counterpart fn-pvc-make))))))

(defthm fn-pacc-ground-u-witness-whole-positive
 (let ((w (fn-pacc-sub-readp-witness *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)))
 (and (equal (v4-ground-u-case nil) '(t t t t t t t t t t t t t))
 (fn-pacc-sub-readp *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)
 (fn-pacc-item-sub-readp *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry*)
 (fn-pacc-profile-admitted-postp *a24p-store* (mv-nth 0 w)
 (fn-pacc-sub-inj *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* (mv-nth 1 w) (mv-nth 2 w))
 *a24p-profile* (fn-pvc-make *a24p-profile*))))
 :hints (("Goal" :use ((:instance fn-pacc-admission-of-two-read-recipes-with-same-headers
 (s *a24p-store*) (sub *a24p-sub-ordinary*) (secret nil) (cfg nil) (carry *fn-pacc-ground-ordinary-carry*)
 (icfg0 *a24p-icfg*) (iclock0 *a24p-clock*) (art0 *a24p-art-ordinary*)
 (art1 (mv-nth 0 (fn-pacc-sub-readp-witness *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)))
 (icfg1 (mv-nth 1 (fn-pacc-sub-readp-witness *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)))
 (iclock1 (mv-nth 2 (fn-pacc-sub-readp-witness *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)))
 (profile *a24p-profile*) (pcarry (fn-pvc-make *a24p-profile*))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-ground-u-whole-positive fn-pacc-read-witness-has-supplied-header-triple
 (:executable-counterpart fn-inj-config-header-limits))))))

(defthm fn-pacc-ground-u-remove-domain
 (and (equal (v4-ground-u-case t) '(t t t t t t t t nil t t nil t))
 (fn-pacc-sub-readp *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)
 (fn-pacc-item-sub-readp *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry*)
 (not (fn-pacc-profile-admitted-postp (fn-sn-initial nil 100) *a24p-art-ordinary*
 (fn-pacc-sub-inj *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-icfg* *a24p-clock*)
 *a24p-profile* (fn-pvc-make *a24p-profile*))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-ground-u-whole-positive (:executable-counterpart v4-ground-u-case)
 (:executable-counterpart fn-pacc-profile-admitted-postp) (:executable-counterpart fn-pacc-sub-inj)
 (:executable-counterpart fn-pvc-make) (:executable-counterpart fn-sn-initial))))))

(defthm fn-pacc-ground-u-witness-remove-domain
 (let ((w (fn-pacc-sub-readp-witness *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)))
 (and (equal (v4-ground-u-case t) '(t t t t t t t t nil t t nil t))
 (fn-pacc-sub-readp *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)
 (fn-pacc-item-sub-readp *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry*)
 (not (fn-pacc-profile-admitted-postp (fn-sn-initial nil 100) (mv-nth 0 w)
 (fn-pacc-sub-inj *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* (mv-nth 1 w) (mv-nth 2 w))
 *a24p-profile* (fn-pvc-make *a24p-profile*)))))
 :hints (("Goal" :use ((:instance fn-pacc-admission-of-two-read-recipes-with-same-headers
 (s (fn-sn-initial nil 100)) (sub *a24p-sub-ordinary*) (secret nil) (cfg nil) (carry *fn-pacc-ground-ordinary-carry*)
 (icfg0 *a24p-icfg*) (iclock0 *a24p-clock*) (art0 *a24p-art-ordinary*)
 (art1 (mv-nth 0 (fn-pacc-sub-readp-witness *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)))
 (icfg1 (mv-nth 1 (fn-pacc-sub-readp-witness *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)))
 (iclock1 (mv-nth 2 (fn-pacc-sub-readp-witness *a24p-sub-ordinary* nil nil *fn-pacc-ground-ordinary-carry* *a24p-h*)))
 (profile *a24p-profile*) (pcarry (fn-pvc-make *a24p-profile*))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-ground-u-remove-domain fn-pacc-read-witness-has-supplied-header-triple
 (:executable-counterpart fn-inj-config-header-limits))))))

; Structural ground witnesses: landing-v3-ground.lisp
(defun fn-pacc-ground-v3-writer-rows () (declare (xargs :guard t :verify-guards nil))
(with-local-stobj fn-arena (mv-let (answer fn-arena) (mv (with-local-stobj fn-hist (mv-let (answer fn-hist) (mv (list
(and (fn-pacc-conns-read-own-headersp (fn-own-make nil nil (fn-own-conns *a24p-opened*) nil nil nil nil nil nil nil nil nil nil nil nil) (fn-own-conns *a24p-opened*)) (fn-pacc-pins-read-own-headersp (fn-own-make nil nil (fn-own-conns *a24p-opened*) nil nil nil nil nil nil nil nil nil nil nil nil)))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*)) (fn-pacc-conn-reads-own-headersp (fn-ocfg-owner *a25-limit-opened*) (car (fn-own-conns *a24p-opened*)))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-asto-with-conn *a25-limit-opened* (car (fn-own-conns *a24p-opened*))))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-crf-with-store *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (mv-let (v0 v1) (fn-oclc-publish *a25-limit-opened* nil (fn-inj-post-bound (fn-sbud-payload-bound *a24p-profile*) (fn-bs-profile-header-limits *a24p-profile*))) (declare (ignore v0)) v1))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-ocl-owner-with-store *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (mv-let (v0 v1) (fn-ocl-publish *a25-limit-opened* nil (fn-inj-post-bound (fn-sbud-payload-bound *a24p-profile*) (fn-bs-profile-header-limits *a24p-profile*))) (declare (ignore v0)) v1))))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-ccp-owner-with-approved *a25-limit-opened* nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-irc-rix-own-complete-enabled *a24p-owner* fn-hist nil)))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-irc-ocfg-prepare-identity *a25-limit-opened* nil nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (cdr (fn-acar-own-advance-result *a24p-owner* nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (cdr (fn-acar-own-outcome *a24p-owner* nil nil))))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-oas-owner-closed *a25-limit-opened* nil))))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-ocln-owner-at-line *a25-limit-opened* nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-ccar-own-complete-enabled *a24p-owner*)))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-ccar-ocfg-prepare-identity *a25-limit-opened* nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (cdr (fn-ocar-own-open *a24p-owner* nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-ocar-own-reader-context *a24p-owner* nil nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-oct-outcome-next *a24p-owner* nil nil nil nil nil nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-oct-transit-next *a24p-owner* nil (car (fn-own-conns *a24p-opened*)) nil nil nil nil nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-oop-outcome-next *a24p-owner* nil nil nil nil nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-oop-transit-next *a24p-owner* nil (car (fn-own-conns *a24p-opened*)) nil nil nil nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-pcar-opc-owner-prepare *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-opc-owner-prepare *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-psrv-prepare-topic *a25-limit-opened* nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-with-view *a24p-owner* nil)))
(fn-pacc-pins-read-own-headersp (fn-orcp-swap-base nil nil))
(and (and (fn-pacc-pins-read-own-headersp nil)) (fn-pacc-pins-read-own-headersp (fn-orcp-swapped-owner nil nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-refresh-ix *a24p-owner* fn-hist)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-rix-own-complete-enabled *a24p-owner* fn-hist)))
(and (fn-pacc-pins-read-own-headersp *a24p-owner*) (fn-pacc-pins-read-own-headersp (mv-let (v0 v1) (fn-osb-install *a24p-owner* *a24p-profile*) (declare (ignore v0)) v1)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*) (fn-pacc-conn-reads-own-headersp *a24p-owner* (car (fn-own-conns *a24p-opened*)))) (fn-pacc-pins-read-own-headersp (cdr (fn-scar-finish-read *a24p-owner* (car (fn-own-conns *a24p-opened*)) nil nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (cadr (fn-scar-own-read-step-full *a24p-owner* nil nil fn-arena))))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-otm-owner-with-allow *a25-limit-opened* nil nil))))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-otm-ocfg-with-refused *a25-limit-opened* nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-refresh *a24p-owner*)))
(and (fn-pacc-conns-read-own-headersp *a24p-owner* (fn-own-conns *a24p-opened*)) (fn-pacc-pins-read-own-headersp (fn-own-set-conns *a24p-owner* (fn-own-conns *a24p-opened*))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-reader-context *a24p-owner* nil nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (cdr (fn-own-open *a24p-owner* nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (cdr (fn-own-open-peer *a24p-owner* nil nil nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-enqueue *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*) (fn-pacc-conn-reads-own-headersp *a24p-owner* (car (fn-own-conns *a24p-opened*)))) (fn-pacc-pins-read-own-headersp (cdr (fn-own-finish-read *a24p-owner* (car (fn-own-conns *a24p-opened*)) nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (cadr (fn-own-read-step-full *a24p-owner* nil nil fn-arena))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (cdr (fn-own-advance-result *a24p-owner* nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-close *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-begin *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-store-step *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-complete *a24p-owner*)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-reopen *a24p-owner* nil nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-observe *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-declare-group *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-with-feeds *a24p-owner* nil)))
(and (fn-pacc-pins-read-own-headersp *a24p-owner*) (fn-pacc-pins-read-own-headersp (fn-own-configure *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-with-node-secret *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-take-submission *a24p-owner*)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (cdr (fn-own-outcome *a24p-owner* nil nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-own-control-outcome *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (cdr (fn-own-transit-outcome *a24p-owner* nil nil nil nil))))
(and (fn-pacc-pins-read-own-headersp *a24p-owner*) (fn-pacc-pins-read-own-headersp (fn-own-step *a24p-owner* nil fn-arena)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-pidx-opc-owner-prepare *a24p-owner* nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-ppc-opc-owner-prepare *a24p-owner* nil nil nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-prc-opc-owner-prepare *a24p-owner* nil nil)))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (fn-rcon-own-store-io *a24p-owner* nil nil)))
(and (fn-pacc-pins-read-own-headersp *a24p-owner*) (fn-pacc-pins-read-own-headersp (fn-own-configure *a24p-owner* (fn-oag-post-config nil (fn-inj-post-bound (fn-sbud-payload-bound *a24p-profile*) (fn-bs-profile-header-limits *a24p-profile*))))))
(and (fn-pacc-pins-read-own-headersp *a24p-owner*) (fn-pacc-pins-read-own-headersp (fn-own-configure *a24p-owner* (fn-inj-make-config-full nil (fn-inj-config-agent (fn-own-config *a24p-owner*)) (fn-inj-config-groups (fn-own-config *a24p-owner*)) (fn-inj-post-bound (fn-sbud-payload-bound *a24p-profile*) (fn-bs-profile-header-limits *a24p-profile*)) (fn-inj-config-listing (fn-own-config *a24p-owner*)) (fn-inj-config-closed (fn-own-config *a24p-owner*))))))
(and (fn-pacc-pins-read-own-headersp *a24p-owner*) (fn-pacc-pins-read-own-headersp (mv-let (v0 v1) (fn-osb-install *a24p-owner* (fn-lim-apply-row *a24p-profile* nil nil)) (declare (ignore v0)) v1)))
(and (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner *a25-limit-opened*))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (cdr (fn-ocar-ocfg-open *a25-limit-opened* nil)))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (car (fn-oct-control *a24p-owner* nil nil))))
(and (and (fn-pacc-pins-read-own-headersp *a24p-owner*)) (fn-pacc-pins-read-own-headersp (cdr (fn-apc-own-outcome *a24p-owner* nil nil nil nil))))) fn-hist) answer)) fn-arena) answer)))

(with-guard-checking-event :none (defthm fn-pacc-ground-v3-all-writer-rows-positive
 (equal (fn-pacc-ground-v3-writer-rows) (quote (t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t t)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-pacc-ground-v3-writer-rows)))))))

; Structural ground witnesses: landing-ground-structural.lisp
(defconst *fn-pacc-ground-open-refused-owner* (fn-own-configure (fn-own-start *a24p-store* 0) *a24p-icfg*))

(defconst *fn-pacc-ground-cap-violating-owner* (fn-own-make *a24p-store* (fn-own-view *a24p-opened*) (fn-own-conns *a24p-opened*) 2 0 nil nil *a24p-clock* nil *a24p-icfg* nil nil nil nil nil))

(with-guard-checking-event :none (defthm fn-pacc-ground-open-positive
 (let ((o *a24p-owner*)) (and (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o))) (let ((pin (fn-own-conn-config (car (fn-own-conns (cdr (fn-own-open o nil))))))) (and (equal pin (fn-own-config o)) (equal (fn-inj-config-header-limits pin) (fn-inj-config-header-limits (fn-own-config o)))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-own-open) (:executable-counterpart fn-own-conns) (:executable-counterpart fn-own-max-conns) (:executable-counterpart fn-own-config) (:executable-counterpart fn-own-conn-config) (:executable-counterpart fn-inj-config-header-limits) (:executable-counterpart fn-pacc-pinned-header-triples) (:executable-counterpart len) (:executable-counterpart nfix) (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart equal) (:executable-counterpart <)))))))

(with-guard-checking-event :none (defthm fn-pacc-ground-open-remove-capacity
 (let ((o *fn-pacc-ground-open-refused-owner*)) (and (not (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o)))) (not (let ((pin (fn-own-conn-config (car (fn-own-conns (cdr (fn-own-open o nil))))))) (and (equal pin (fn-own-config o)) (equal (fn-inj-config-header-limits pin) (fn-inj-config-header-limits (fn-own-config o))))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-own-open) (:executable-counterpart fn-own-conns) (:executable-counterpart fn-own-max-conns) (:executable-counterpart fn-own-config) (:executable-counterpart fn-own-conn-config) (:executable-counterpart fn-inj-config-header-limits) (:executable-counterpart fn-pacc-pinned-header-triples) (:executable-counterpart len) (:executable-counterpart nfix) (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart equal) (:executable-counterpart <)))))))

(with-guard-checking-event :none (defthm fn-pacc-ground-cap-positive
 (let ((o *a24p-opened*)) (and (<= (len (fn-own-conns o)) (nfix (fn-own-max-conns o))) (<= (len (fn-pacc-pinned-header-triples (fn-own-conns o))) (nfix (fn-own-max-conns o)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-own-open) (:executable-counterpart fn-own-conns) (:executable-counterpart fn-own-max-conns) (:executable-counterpart fn-own-config) (:executable-counterpart fn-own-conn-config) (:executable-counterpart fn-inj-config-header-limits) (:executable-counterpart fn-pacc-pinned-header-triples) (:executable-counterpart len) (:executable-counterpart nfix) (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart equal) (:executable-counterpart <)))))))

(with-guard-checking-event :none (defthm fn-pacc-ground-cap-remove-capacity
 (let ((o *fn-pacc-ground-cap-violating-owner*)) (and (not (<= (len (fn-own-conns o)) (nfix (fn-own-max-conns o)))) (not (<= (len (fn-pacc-pinned-header-triples (fn-own-conns o))) (nfix (fn-own-max-conns o))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-own-open) (:executable-counterpart fn-own-conns) (:executable-counterpart fn-own-max-conns) (:executable-counterpart fn-own-config) (:executable-counterpart fn-own-conn-config) (:executable-counterpart fn-inj-config-header-limits) (:executable-counterpart fn-pacc-pinned-header-triples) (:executable-counterpart len) (:executable-counterpart nfix) (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart equal) (:executable-counterpart <)))))))

(defthm fn-pacc-ground-owner-read-positive
 (and (fn-pacc-owner-value-readsp *v4-before*) (fn-pacc-owner-value-readsp *v4-after*))
 :hints (("Goal" :use fn-pacc-peritem-64-to-10-positive
 :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-osb-install) (:executable-counterpart fn-ocfg-owner) (:executable-counterpart mv-nth))))))

(defthm fn-pacc-ground-owner-read-remove-queue
 (let ((o (fn-own-enqueue (fn-ocfg-owner *a25-limit-opened*) *v4-bad-sub*)))
 (and (fn-pacc-pins-read-own-headersp o)
 (fn-pacc-inflight-readp (fn-own-inflight o) nil nil nil)
 (not (fn-pacc-queue-readp (fn-own-queue o) nil nil nil))
 (not (fn-pacc-owner-value-readsp o))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-every-owner-pin-reads-own-headers fn-pacc-malformed-item-has-no-read-witness
 fn-pacc-owner-value-readsp fn-pacc-queue-readp fn-pacc-local-sub-readp fn-pacc-inflight-readp
 (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-own-queue)
 (:executable-counterpart fn-own-inflight) (:executable-counterpart fn-ocfg-owner)
 (:executable-counterpart fn-psub-unpack-sub) (:executable-counterpart fn-own-sub-source-context)
 (:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp)
 (:executable-counterpart fn-peer-submissionp) car-cons cdr-cons)))))

; Additional whole witnesses: landing-ground-pointwise.lisp
(defthm fn-pacc-malformed-item-has-no-pointwise-read-witness
 (not (fn-pacc-sub-readp *v4-bad-sub* secret cfg carry h))
 :hints (("Goal" :use ((:instance fn-pacc-sub-readp-fixes-shape (sub *v4-bad-sub*)
 (take-config cfg) (parse-carry carry) (read-limits h)))
 :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart fn-own-sub-shapep))))))

(defthm fn-pacc-ground-eq-positive-at-item-triple
 (and (fn-pacc-sub-readp *a24p-sub-ordinary* nil nil nil '(64 256 16384))
 (fn-pacc-single-queue-readp (fn-own-queue *v4-before*) nil nil nil '(64 256 16384))
 (fn-pacc-single-queue-readp (fn-own-queue (fn-own-enqueue *v4-before* *a24p-sub-ordinary*)) nil nil nil '(64 256 16384)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-ordinary-fixture-has-whole-read-witness fn-pacc-many-fixture-has-whole-read-witness
 fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp (:executable-counterpart fn-own-queue)
 (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-psub-unpack-sub)
 (:executable-counterpart fn-own-sub-source-context) (:executable-counterpart fn-own-sub-decision)
 (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-peer-submissionp) car-cons cdr-cons)))))

(defthm fn-pacc-ground-eq-remove-item-read-at-item-triple
 (and (not (fn-pacc-sub-readp *v4-bad-sub* nil nil nil '(64 256 16384)))
 (fn-pacc-single-queue-readp (fn-own-queue *v4-before*) nil nil nil '(64 256 16384))
 (not (fn-pacc-single-queue-readp (fn-own-queue (fn-own-enqueue *v4-before* *v4-bad-sub*)) nil nil nil '(64 256 16384))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-malformed-item-has-no-pointwise-read-witness fn-pacc-many-fixture-has-whole-read-witness
 fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp (:executable-counterpart fn-own-queue)
 (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-psub-unpack-sub)
 (:executable-counterpart fn-own-sub-source-context) (:executable-counterpart fn-own-sub-decision)
 (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-peer-submissionp) car-cons cdr-cons)))))

(defthm fn-pacc-ground-er-whole-positive-at-item-triple
 (and (equal (v4-ground-er-case nil) '(t t t t t t t t t))
 (fn-pacc-single-queue-readp (fn-own-queue (fn-own-enqueue *a24p-owner* *a24p-sub-ordinary*)) nil nil nil '(64 256 16384))
 (fn-pacc-single-queue-readp (fn-own-queue (fn-pacc-ground-er-output *a24p-sub-ordinary*)) nil nil nil '(64 256 16384)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-ordinary-fixture-has-whole-read-witness fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp
 (:executable-counterpart v4-ground-er-case) (:executable-counterpart fn-own-queue)
 (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-pacc-ground-er-output)
 (:executable-counterpart fn-psub-unpack-sub) (:executable-counterpart fn-own-sub-source-context)
 (:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp)
 (:executable-counterpart fn-peer-submissionp) car-cons cdr-cons)))))

(defthm fn-pacc-ground-er-remove-queue-read-at-item-triple
 (and (equal (v4-ground-er-case t) '(t t t t t t nil nil nil))
 (not (fn-pacc-single-queue-readp (fn-own-queue (fn-own-enqueue *a24p-owner* *v4-bad-sub*)) nil nil nil '(64 256 16384)))
 (not (fn-pacc-single-queue-readp (fn-own-queue (fn-pacc-ground-er-output *v4-bad-sub*)) nil nil nil '(64 256 16384))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-malformed-item-has-no-pointwise-read-witness fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp
 (:executable-counterpart v4-ground-er-case) (:executable-counterpart fn-own-queue)
 (:executable-counterpart fn-own-enqueue) (:executable-counterpart fn-pacc-ground-er-output)
 (:executable-counterpart fn-psub-unpack-sub) (:executable-counterpart fn-own-sub-source-context)
 (:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp)
 (:executable-counterpart fn-peer-submissionp) car-cons cdr-cons)))))

; Additional whole witnesses: landing-ground-final.lisp
(defun fn-pacc-ground-e-case (awaiting)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-arena
 (mv-let (answer fn-arena)
 (let* ((ps (fn-post-make-session (fn-nntp-open-session *a24p-archive*) awaiting))
 (d *a24p-d-ordinary*)
 (r (fn-nntp-post-step ps *a24p-archive* *a24p-icfg* *a24p-clock* *a24p-clock*
 (list :article *a24p-body-ordinary*) fn-arena))
 (sub (fn-own-sub-make-author 0 0 nil (fn-post-result-submission r) nil nil
 (fn-own-served-source-context (fn-post-result-submission r)))))
 (mv (list (fn-arena-p fn-arena) (fn-post-sessionp ps) (fn-post-session-awaiting ps)
 (fn-apc-p nil) (fn-inj-injectedp d) (equal (fn-post-result-submission r) d) sub) fn-arena)) answer)))

(with-guard-checking-event :none
 (defthm fn-pacc-ground-e-whole-positive
 (and (equal (take 6 (fn-pacc-ground-e-case t)) '(t t t t t t))
 (fn-pacc-sub-readp (nth 6 (fn-pacc-ground-e-case t)) nil nil nil *a24p-h*))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-ordinary-fixture-has-whole-read-witness (:executable-counterpart fn-pacc-ground-e-case)
 (:executable-counterpart take) (:executable-counterpart nth)))))))

(with-guard-checking-event :none
 (defthm fn-pacc-ground-e-remove-awaiting
 (and (equal (take 6 (fn-pacc-ground-e-case nil)) '(t t nil t t nil))
 (not (fn-pacc-sub-readp (nth 6 (fn-pacc-ground-e-case nil)) nil nil nil *a24p-h*)))
 :hints (("Goal" :use ((:instance fn-pacc-sub-readp-fixes-shape
 (sub (nth 6 (fn-pacc-ground-e-case nil))) (secret nil) (take-config nil) (parse-carry nil) (read-limits *a24p-h*)))
 :in-theory (union-theories (theory 'minimal-theory)
 '((:executable-counterpart fn-pacc-ground-e-case) (:executable-counterpart take)
 (:executable-counterpart nth) (:executable-counterpart fn-own-sub-decision)
 (:executable-counterpart fn-inj-injectedp)))))))

(defthm fn-pacc-ground-inflight-whole-positive
 (fn-pacc-inflight-readp *v4-many-sub* nil nil nil)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-inflight-readp fn-pacc-local-sub-readp fn-pacc-many-fixture-has-whole-read-witness)))))

(defthm fn-pacc-ground-inflight-remove-item-read
 (and (equal (fn-own-sub-source-context *v4-bad-sub*) :post-d25)
 (fn-inj-injectedp (fn-own-sub-decision *v4-bad-sub*))
 (not (fn-peer-submissionp (fn-own-sub-decision *v4-bad-sub*)))
 (not (fn-pacc-inflight-readp *v4-bad-sub* nil nil nil)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-inflight-readp fn-pacc-local-sub-readp fn-pacc-malformed-item-has-no-read-witness
 (:executable-counterpart fn-own-sub-source-context) (:executable-counterpart fn-own-sub-decision)
 (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-peer-submissionp))))))

(defthm fn-pacc-owner-readsp-value-projection-unfolds
 (equal (fn-pacc-owner-readsp state)
 (fn-pacc-owner-value-readsp (fn-ocfg-owner (fn-owner-ocfg state))))
 :hints (("Goal" :in-theory (enable fn-pacc-owner-readsp))))

(with-guard-checking-event :none
 (defthm fn-pacc-ground-cap-premise-inhabited-by-owner-relation
 (and (fn-own-relation *a24p-opened*)
 (<= (len (fn-own-conns *a24p-opened*)) (nfix (fn-own-max-conns *a24p-opened*))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '((:executable-counterpart fn-own-relation) (:executable-counterpart fn-own-conns)
 (:executable-counterpart fn-own-max-conns) (:executable-counterpart len) (:executable-counterpart nfix)))))))

; Final historical v3 startup and live-apply removal evidence.
(defthm fn-pacc-single-v3-startup-install-establishes-owner-reads (let* ((oc (fn-ock-install replayed opened max-conns)) (o2 (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile))) (h (fn-bs-profile-header-limits profile))) (implies (and (not (equal oc :fault)) (fn-bs-profile-admittedp profile)) (and (fn-pacc-pins-read-own-headersp o2) (fn-pacc-single-queue-readp (fn-own-queue o2) nil nil nil h) (fn-pacc-single-local-sub-readp (fn-own-inflight o2) nil nil nil h))))
 :hints (("Goal" :do-not-induct t :use fn-pacc-recovered-owner-has-no-local-work
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-every-owner-pin-reads-own-headers fn-pacc-osb-install-keeps-queue-and-inflight
 fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp
 fn-own-sub-source-context fn-own-sub-decision fn-inj-injectedp fn-inj-decision-status
 fn-inj-nth fn-inj-car fn-inj-cdr fn-ag-car fn-ag-cdr nfix zp
 (:executable-counterpart consp) (:executable-counterpart equal))))))

(with-guard-checking-event :none
 (defthm fn-pacc-ground-live-apply-remove-installed
 (mv-let (verdict next) (fn-osb-install *v4-before* nil)
 (and (not (equal verdict :installed))
 (not (and (equal (fn-inj-config-header-limits (fn-own-config next)) (fn-bs-profile-header-limits nil))
 (equal (fn-own-conns next) (fn-own-conns *v4-before*))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '((:executable-counterpart fn-osb-install) (:executable-counterpart fn-own-config)
 (:executable-counterpart fn-inj-config-header-limits) (:executable-counterpart fn-bs-profile-header-limits)
 (:executable-counterpart fn-own-conns) (:executable-counterpart equal) car-cons cdr-cons))))))

; Startup inhabitation and proof that no startup reader-hypothesis removal exists.
(with-guard-checking-event :none
 (defthm fn-pacc-ground-startup-whole-positive
 (let* ((configs (list *fn-cfg-default-record*))
 (oc (fn-ock-install (fn-cpr-replay configs nil) (fn-cpo-open-observed configs 0 nil) 4))
 (next (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) *a25-limit-profile*)))
 (h (fn-bs-profile-header-limits *a25-limit-profile*)))
 (and (not (equal oc :fault)) (fn-bs-profile-admittedp *a25-limit-profile*)
 (fn-pacc-pins-read-own-headersp next)
 (fn-pacc-single-queue-readp (fn-own-queue next) nil nil nil h)
 (fn-pacc-single-local-sub-readp (fn-own-inflight next) nil nil nil h)
 (fn-pacc-owner-value-readsp next)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-every-owner-pin-reads-own-headers fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp
 fn-pacc-owner-value-readsp fn-pacc-queue-readp fn-pacc-inflight-readp fn-pacc-local-sub-readp
 (:executable-counterpart fn-cpr-replay) (:executable-counterpart fn-cpo-open-observed)
 (:executable-counterpart fn-ock-install) (:executable-counterpart fn-osb-install)
 (:executable-counterpart fn-ocfg-owner) (:executable-counterpart fn-own-queue)
 (:executable-counterpart fn-own-inflight) (:executable-counterpart fn-own-sub-source-context)
 (:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp)
 (:executable-counterpart fn-peer-submissionp) (:executable-counterpart fn-bs-profile-admittedp)
 (:executable-counterpart fn-bs-profile-header-limits) (:executable-counterpart mv-nth)
 car-cons cdr-cons))))))

(with-guard-checking-event :none
 (defthm fn-pacc-ground-unconnected-profile-install-positive
 (and (fn-bs-profile-admittedp *a25-limit-profile*)
 (not (consp (fn-own-conns *a24p-owner*)))
 (fn-pacc-pins-read-own-headersp (mv-nth 1 (fn-osb-install *a24p-owner* *a25-limit-profile*))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-every-owner-pin-reads-own-headers (:executable-counterpart fn-bs-profile-admittedp)
 (:executable-counterpart fn-own-conns) (:executable-counterpart consp)))))))

(defthm fn-pacc-single-v3-startup-read-conclusion-is-unconditional
 (let* ((oc (fn-ock-install replayed opened max-conns))
 (next (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile)))
 (h (fn-bs-profile-header-limits profile)))
 (and (fn-pacc-pins-read-own-headersp next)
 (fn-pacc-single-queue-readp (fn-own-queue next) nil nil nil h)
 (fn-pacc-single-local-sub-readp (fn-own-inflight next) nil nil nil h)))
 :hints (("Goal" :do-not-induct t :cases ((equal (fn-ock-install replayed opened max-conns) :fault))
 :use fn-pacc-recovered-owner-has-no-local-work
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-every-owner-pin-reads-own-headers fn-pacc-osb-install-keeps-queue-and-inflight
 fn-pacc-single-queue-readp fn-pacc-single-local-sub-readp
 (:executable-counterpart fn-ocfg-owner) (:executable-counterpart fn-own-queue)
 (:executable-counterpart fn-own-inflight) (:executable-counterpart fn-own-sub-source-context)
 (:executable-counterpart fn-own-sub-decision) (:executable-counterpart fn-inj-injectedp))))))

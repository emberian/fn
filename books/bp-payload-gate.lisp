; fn: no payload-dependent BP work without a durable canonical pin, and never
; a tombstone as payload (RECLAIM-RETENTION, 2026-10-03).
;
; Reclaim honours the canonical retention pins of the Store
; (books/store-reclaim-holders fn-rcl-store-holders-never-reclaim-a-forward-
; pinned-article).  The workflow image's node is the Store's node with the
; workflow journal replayed over it, and an FNWF :undertake record
; (books/bp-release fn-bprl-undertake, `app-journal workflow-undertake')
; pins only that image: a pin reclaim never sees.  And the request a
; workflow attempt builds reads the article's bytes from its node at that
; moment (books/bp-outbound fn-bpo-request-message); the ADU codec accepts
; any record payload (books/bp-adu fn-bpa-requestp), a reclaim tombstone
; included.  So before this gate a later attempt of a work whose article was
; reclaimed sent its tombstone as the forwarded article.
;
; Two refusals, each by name, at the entries that PRODUCE payload -- never
; in replay, where a historical route or observation of a work whose pin a
; receipt released and whose article was then reclaimed must still replay
; (books/bp-ion-workflow fn-bpiw-route-admissiblep reads the request
; message, not this gate):
;
;   :forward-pin-not-durable  the work's :forward pin, with its required
;                             evidence, is not live in the CANONICAL node
;                             (the Store's: the owner's Store on the shared
;                             owner path, the opened Store on the standalone
;                             one), whatever the workflow image holds;
;   :article-reclaimed        the article the ADU carries is a reclaim
;                             tombstone (read from the ADU's own decoding:
;                             the bytes that would leave).
;
; KEYSTONE fn-bppg-request-gate-sends-only-pinned-live-payload: a plan the
; gate passes is ACL2's plan, its work is canonically pinned, and the
; article its ADU carries is not a tombstone.
(in-package "ACL2")
(include-book "bp-request-plan")
(include-book "bp-release")
(include-book "reclaim-tombstone")

; The work's :forward pin, with its required evidence, is live in CANON.
(defun fn-bppg-canonically-pinnedp (canon s work-id)
  (declare (xargs :guard t :verify-guards nil))
  (let ((work (fn-bp-find-work work-id (fn-bp-state-works s))))
    (and (consp work)
         (fn-bprl-work-pinnedp (fn-bprl-with-node s canon) work)
         t)))

; The article an encoded request ADU carries is a reclaim tombstone.
(defun fn-bppg-adu-tombstonep (adu)
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-bpa-decode-exact adu)))
    (and (consp d) (equal (car d) :ok)
         (fn-rcl-tombstonep (fn-bpa-request-article (cadr d))))))

; The article bytes of the work's article in S's node (what the next ADU
; would carry), a tombstone.
(defun fn-bppg-article-tombstonep (s work-id fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let* ((work (fn-bp-find-work work-id (fn-bp-state-works s)))
         (article (fn-find-article
                   (fn-bp-work-msgid work)
                   (fn-state-articles (fn-node-acceptance (fn-bp-state-node s))))))
    (fn-rcl-tombstonep (fn-bpo-article-octets article fn-arena))))

; The generic request (`bp-obligation request'): PLAN is fn-bprq-plan's (or
; a refusal already).  A :request plan passes only pinned and live.
(defun fn-bppg-request-gate (canon s work-id plan)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp plan) (equal (car plan) :request))
      (cond ((not (fn-bppg-canonically-pinnedp canon s work-id))
             (list :refused :forward-pin-not-durable))
            ((fn-bppg-adu-tombstonep (fn-bprq-plan-adu plan))
             (list :refused :article-reclaimed))
            (t plan))
    plan))

; The ION attempt (`app-journal workflow-ion-submit'): PLAN is
; fn-bprq-ion-attempt-plan's, (retry attempt) or nil; nothing is published
; before it.  Refused by name the same way, the article read from S's node.
(defun fn-bppg-ion-attempt-gate (canon s work-id plan fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp plan)
      (cond ((not (fn-bppg-canonically-pinnedp canon s work-id))
             (list :refused :forward-pin-not-durable))
            ((fn-bppg-article-tombstonep s work-id fn-arena)
             (list :refused :article-reclaimed))
            (t plan))
    plan))

; The ION request ADU: nil (the host refuses) when it would carry a
; tombstone.
(defun fn-bppg-ion-adu (adu)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-bppg-adu-tombstonep adu) nil adu))

;  KEYSTONE.  Subject: fn-bppg-request-gate, which host/bp-release-owner-
; host.lisp fn-owner-workflow-request-plan returns to host/native/
; bp-obligation.lisp fnn-bpo-request-publish (the only producer of the
; generic request's ADU).  A :request it answers is the plan ACL2 made, the
; work's :forward pin is live in the canonical node, and the article the ADU
; carries is not a reclaim tombstone.
(defthm fn-bppg-request-gate-sends-only-pinned-live-payload
  (let ((out (fn-bppg-request-gate canon s work-id plan)))
    (implies (and (consp out) (equal (car out) :request))
             (and (equal out plan)
                  (fn-bppg-canonically-pinnedp canon s work-id)
                  (not (fn-bppg-adu-tombstonep (fn-bprq-plan-adu out))))))
  :hints (("Goal" :in-theory (disable fn-bppg-canonically-pinnedp
                                      fn-bppg-adu-tombstonep fn-bprq-plan-adu))))

; A refusal is by name and never a plan.
(defthm fn-bppg-request-gate-refusals-are-named
  (let ((out (fn-bppg-request-gate canon s work-id plan)))
    (implies (not (equal out plan))
             (or (equal out '(:refused :forward-pin-not-durable))
                 (equal out '(:refused :article-reclaimed)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bppg-canonically-pinnedp
                                      fn-bppg-adu-tombstonep fn-bprq-plan-adu))))

(local
 (defthm fn-bppg-adu-tombstonep-of-nil
   (not (fn-bppg-adu-tombstonep nil))))

;  KEYSTONE (ION).  An ION attempt plan the gate passes is ACL2's, its work
; is canonically pinned, and the article its ADU would carry is not a
; tombstone; the ADU entry never answers a tombstone-carrying ADU.
(defthm fn-bppg-ion-gates-send-only-pinned-live-payload
  (and (let ((out (fn-bppg-ion-attempt-gate canon s work-id plan fn-arena)))
         (implies (and (consp out) (not (equal (car out) :refused)))
                  (and (equal out plan)
                       (fn-bppg-canonically-pinnedp canon s work-id)
                       (not (fn-bppg-article-tombstonep s work-id fn-arena)))))
       (not (fn-bppg-adu-tombstonep (fn-bppg-ion-adu adu))))
  :hints (("Goal" :in-theory (disable fn-bppg-canonically-pinnedp
                                      fn-bppg-article-tombstonep
                                      fn-bppg-adu-tombstonep))))

; Experimental fixed-controller P3 root-only admission machine.
; Preparation constructs a proposed Store event; only validated completion
; changes the projection. This book does not publish Store bytes by itself.
(in-package "ACL2")
(include-book "topic-history-authorship")

(defconst *fn-th-max-anchors* 16)
(defconst *fn-th-max-report-quota* 64)

; Historical T10 coordinates name one already accepted exact source.
(defun fn-th-auth-ref-of (event)
  (declare (xargs :guard t))
  (list (fn-stxa-sequence event) (fn-stxa-txid event)
        (fn-stxa-authored-id event) (fn-stxa-sequence event)
        (fn-stxa-keyring-generation event) (fn-stxa-profile event)))

; The event's source reference is separately re-resolved against T10 on
; replay. These shapes are deliberately small and omit application bytes.
(defun fn-th-anchor-event (sequence txid generation event quota caller)
  (declare (xargs :guard t))
  (list :topic-anchor sequence txid generation
        (fn-stxa-authored-id event) (fn-th-auth-ref-of event) quota caller))
(defun fn-th-report-event (sequence txid generation event report)
  (declare (xargs :guard t))
  (list :topic-admit sequence txid generation
        (fn-th-at 1 report) (fn-stxa-authored-id event)
        (fn-th-at 2 report) (fn-th-auth-ref-of event)
        (fn-th-at 3 report)))

; Projection anchors are bounded records:
; (:anchor topic controller keyset domain authors root-ref quota remaining
;          selected-policy status admissions).
(defun fn-th-anchor (root-id root auth-ref quota)
  (declare (xargs :guard t))
  (list :anchor root-id (fn-th-at 2 root) (fn-th-at 3 root)
        (fn-th-at 4 root) (fn-th-at 5 root) auth-ref quota quota
        root-id :active nil))
(defun fn-th-anchor-topic (anchor)
  (declare (xargs :guard t)) (fn-th-at 1 anchor))
(defun fn-th-anchor-reports (anchor)
  (declare (xargs :guard t)) (fn-th-at 11 anchor))
(defun fn-th-find-anchor (topic anchors)
  (declare (xargs :guard t))
  (if (consp anchors)
      (if (equal topic (fn-th-anchor-topic (car anchors)))
          (car anchors)
        (fn-th-find-anchor topic (cdr anchors)))
    nil))

; Historical admission records retain the exact policy and T10 source ref:
; (:admitted topic report-id policy-id auth-ref parents event-sequence).
(defun fn-th-admission (event)
  (declare (xargs :guard t))
  (list :admitted (fn-th-at 4 event) (fn-th-at 5 event)
        (fn-th-at 6 event) (fn-th-at 7 event) (fn-th-at 8 event)
        (fn-th-at 1 event)))
(defun fn-th-find-admission (source-id admissions)
  (declare (xargs :guard t))
  (if (consp admissions)
      (if (equal source-id (fn-th-at 2 (car admissions)))
          (car admissions)
        (fn-th-find-admission source-id (cdr admissions)))
    nil))
(defun fn-th-member-author-p (author authors)
  (declare (xargs :guard t))
  (if (consp authors)
      (or (equal author (car authors))
          (fn-th-member-author-p author (cdr authors)))
    nil))
(defun fn-th-parents-admitted-p (parents admissions topic sequence)
  (declare (xargs :guard t))
  (if (consp parents)
      (let ((prior (fn-th-find-admission (car parents) admissions)))
        (and prior
             (equal (fn-th-at 1 prior) topic)
             (natp (fn-th-at 6 prior))
             (< (fn-th-at 6 prior) (nfix sequence))
             (fn-th-parents-admitted-p (cdr parents) admissions
                                       topic sequence)))
    (null parents)))

(defun fn-th-prepare-anchor
    (sequence txid generation accepted snapshot caller installed-admin
              quota anchors)
  (declare (xargs :guard t))
  (let* ((selected (fn-th-select-accepted-event accepted snapshot))
         (value (and (fn-stmt-okp selected) (fn-stmt-value selected)))
         (root (fn-th-at 0 value))
         (topic (fn-stxa-authored-id accepted)))
    (cond ((not (and (fn-th-exact-octets-p caller 32)
                    (equal caller installed-admin)))
           (fn-stmt-error :administrator))
          ((not (and (natp sequence) (natp txid) (natp generation)))
           (fn-stmt-error :coordinates))
          ((not (and (posp quota) (<= quota *fn-th-max-report-quota*)))
           (fn-stmt-error :quota))
          ((or (not (true-listp anchors))
               (<= *fn-th-max-anchors* (len anchors)))
           (fn-stmt-error :anchor-capacity))
          ((not (fn-stmt-okp selected)) (fn-stmt-error :authorship))
          ((not (and (equal (fn-th-at 0 root) :root)
                     (equal (fn-th-at 2 value) :controller-matched)))
           (fn-stmt-error :controller))
          ((fn-th-find-anchor topic anchors) (fn-stmt-error :already-anchored))
          (t (fn-stmt-ok
              (fn-th-anchor-event sequence txid generation accepted quota
                                  caller))))))

(defun fn-th-prepare-report
    (sequence txid generation accepted snapshot anchors)
  (declare (xargs :guard t))
  (let* ((selected (fn-th-select-accepted-event accepted snapshot))
         (value (and (fn-stmt-okp selected) (fn-stmt-value selected)))
         (report (fn-th-at 0 value))
         (author (fn-th-at 1 value))
         (topic (fn-th-at 1 report))
         (anchor (fn-th-find-anchor topic anchors))
         (event (fn-th-report-event sequence txid generation accepted report))
         (prior (and anchor (fn-th-find-admission
                             (fn-stxa-authored-id accepted)
                             (fn-th-anchor-reports anchor)))))
    (cond ((not (and (natp sequence) (natp txid) (natp generation)))
           (fn-stmt-error :coordinates))
          ((not (fn-stmt-okp selected)) (fn-stmt-error :authorship))
          ((not (equal (fn-th-at 0 report) :report))
           (fn-stmt-error :not-report))
          ((not anchor) (fn-stmt-error :unanchored))
          ; Historical exact retries precede current-policy checks.
          (prior
           (if (and (equal (fn-th-at 3 prior) (fn-th-at 6 event))
                    (equal (fn-th-at 2 prior) (fn-th-at 5 event))
                    (equal (fn-th-at 4 prior) (fn-th-at 7 event)))
               (list :replayed-historical prior)
             (fn-stmt-error :source-conflict)))
          ((not (equal (fn-th-at 10 anchor) :active))
           (fn-stmt-error :contested))
          ((not (equal (fn-th-at 9 anchor) (fn-th-at 2 report)))
           (fn-stmt-error :stale-policy))
          ((not (fn-th-member-author-p author (fn-th-at 5 anchor)))
           (fn-stmt-error :not-author))
          ((not (fn-th-parents-admitted-p
                 (fn-th-at 3 report) (fn-th-anchor-reports anchor)
                 topic sequence))
           (fn-stmt-error :parents))
          ((not (posp (fn-th-at 8 anchor)))
           (fn-stmt-error :quota))
          (t (fn-stmt-ok event)))))

(defun fn-th-anchor-with-admission (anchor event)
  (declare (xargs :guard t))
  (list :anchor (fn-th-at 1 anchor) (fn-th-at 2 anchor)
        (fn-th-at 3 anchor) (fn-th-at 4 anchor) (fn-th-at 5 anchor)
        (fn-th-at 6 anchor) (fn-th-at 7 anchor)
        (1- (nfix (fn-th-at 8 anchor))) (fn-th-at 9 anchor)
        (fn-th-at 10 anchor)
        (cons (fn-th-admission event) (fn-th-anchor-reports anchor))))
(defun fn-th-replace-anchor (topic replacement anchors)
  (declare (xargs :guard t))
  (if (consp anchors)
      (if (equal topic (fn-th-anchor-topic (car anchors)))
          (cons replacement (cdr anchors))
        (cons (car anchors)
              (fn-th-replace-anchor topic replacement (cdr anchors))))
    nil))

; Completion/recovery passes the prior accepted T10 event and snapshot. A
; forged or stale topic event cannot update the carried projection merely by
; having valid bytes: it must equal the currently prepared result.
(defun fn-th-commit-anchor
    (topic-event accepted snapshot installed-admin anchors)
  (declare (xargs :guard t))
  (let* ((prepared
          (fn-th-prepare-anchor
           (fn-th-at 1 topic-event) (fn-th-at 2 topic-event)
           (fn-th-at 3 topic-event) accepted snapshot
           (fn-th-at 7 topic-event) installed-admin
           (fn-th-at 6 topic-event) anchors))
         (selected (fn-th-select-accepted-event accepted snapshot)))
    (if (and (fn-stmt-okp prepared)
             (equal topic-event (fn-stmt-value prepared)))
        (fn-stmt-ok
         (cons (fn-th-anchor (fn-stxa-authored-id accepted)
                             (fn-th-at 0 (fn-stmt-value selected))
                             (fn-th-auth-ref-of accepted)
                             (fn-th-at 6 topic-event))
               anchors))
      (fn-stmt-error :anchor-event))))
(defun fn-th-commit-report (topic-event accepted snapshot anchors)
  (declare (xargs :guard t))
  (let ((prepared
         (fn-th-prepare-report
          (fn-th-at 1 topic-event) (fn-th-at 2 topic-event)
          (fn-th-at 3 topic-event) accepted snapshot anchors)))
    (if (and (fn-stmt-okp prepared)
             (equal topic-event (fn-stmt-value prepared)))
        (let* ((topic (fn-th-at 4 topic-event))
               (anchor (fn-th-find-anchor topic anchors)))
          (fn-stmt-ok
           (fn-th-replace-anchor topic
                                 (fn-th-anchor-with-admission anchor topic-event)
                                 anchors)))
      (fn-stmt-error :admission-event))))

(defthm fn-th-commit-anchor-requires-exact-preparation
  (implies (fn-stmt-okp
            (fn-th-commit-anchor topic-event accepted snapshot
                                 installed-admin anchors))
           (equal topic-event
                  (fn-stmt-value
                   (fn-th-prepare-anchor
                    (fn-th-at 1 topic-event) (fn-th-at 2 topic-event)
                    (fn-th-at 3 topic-event) accepted snapshot
                    (fn-th-at 7 topic-event)
                    installed-admin (fn-th-at 6 topic-event) anchors))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-th-commit-anchor)
                (fn-th-prepare-anchor fn-th-select-accepted-event)))))
(defthm fn-th-commit-report-requires-exact-preparation
  (implies (fn-stmt-okp
            (fn-th-commit-report topic-event accepted snapshot anchors))
           (equal topic-event
                  (fn-stmt-value
                   (fn-th-prepare-report
                    (fn-th-at 1 topic-event) (fn-th-at 2 topic-event)
                    (fn-th-at 3 topic-event) accepted snapshot anchors))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-th-commit-report)
                (fn-th-prepare-report fn-th-select-accepted-event)))))

(defthm fn-th-fresh-report-is-grounded-in-current-root
  (implies
   (fn-stmt-okp
    (fn-th-prepare-report sequence txid generation accepted snapshot anchors))
   (let* ((selected (fn-th-select-accepted-event accepted snapshot))
          (value (fn-stmt-value selected))
          (report (fn-th-at 0 value))
          (author (fn-th-at 1 value))
          (topic (fn-th-at 1 report))
          (anchor (fn-th-find-anchor topic anchors)))
     (and (fn-stmt-okp selected)
          (equal (fn-th-at 0 report) :report)
          anchor
          (equal (fn-th-at 10 anchor) :active)
          (equal (fn-th-at 9 anchor) (fn-th-at 2 report))
          (fn-th-member-author-p author (fn-th-at 5 anchor))
          (fn-th-parents-admitted-p
           (fn-th-at 3 report) (fn-th-anchor-reports anchor)
           topic sequence)
          (posp (fn-th-at 8 anchor)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-th-prepare-report fn-stmt-ok fn-stmt-okp)
                (fn-th-select-accepted-event fn-th-verified-author-ref
                 fn-th-host-inspect-source)))))

; A historical retry is the exact admission already in this anchor. The
; source is selected and bound before this branch, and the branch precedes
; current policy/roster/quota checks. It proposes no Store event.
(defthm fn-th-report-retry-returns-retained-admission
  (implies
   (equal (car (fn-th-prepare-report
                sequence txid generation accepted snapshot anchors))
          :replayed-historical)
   (let* ((selected (fn-th-select-accepted-event accepted snapshot))
          (report (fn-th-at 0 (fn-stmt-value selected)))
          (anchor (fn-th-find-anchor (fn-th-at 1 report) anchors))
          (prior (fn-th-find-admission
                  (fn-stxa-authored-id accepted)
                  (fn-th-anchor-reports anchor))))
     (and (fn-stmt-okp selected)
          prior
          (equal (fn-th-prepare-report
                  sequence txid generation accepted snapshot anchors)
                 (list :replayed-historical prior))
          (equal (fn-th-at 4 prior) (fn-th-auth-ref-of accepted)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-th-prepare-report fn-stmt-ok)
                (fn-th-select-accepted-event fn-th-auth-ref-of
                 fn-th-find-anchor fn-th-find-admission)))))

(defthm fn-th-replace-anchor-preserves-distinct-topic
  (implies (and (not (equal topic other))
                (equal (fn-th-anchor-topic replacement) topic))
           (equal (fn-th-find-anchor
                   other (fn-th-replace-anchor topic replacement anchors))
                  (fn-th-find-anchor other anchors)))
  :hints (("Goal" :induct (fn-th-replace-anchor topic replacement anchors)
           :in-theory (enable fn-th-replace-anchor fn-th-find-anchor))))

; Actual POST -> persisted raw location -> CNS FETCH and READ.
; A complete, well-formed same-length alternate article replaces device
; bytes only. The original published row/commitment and requested MID stay
; fixed. Positive checks exact output bytes, not merely an accepted status.
; Source-only until the current closure gate executes this fixture.
(in-package "ACL2")
(include-book "../books/owed-cursor")
(include-book "../books/assembly-attach")
(include-book "fnct-client")
(assert-event
 (and (equal (fn2-cns-item-binding-answer :found *fn2-fnct-item-record* nil :ok :ok 32 0) :lease)
      (equal (fn2-cns-item-binding-answer :found *fn2-fnct-item-record* t :ok :stale 32 0) :retry)
      (equal (fn2-cns-item-binding-answer :found *fn2-fnct-item-record* t :ok :ok 31 0) :fault)
      (equal (fn2-cns-item-binding-answer :found *fn2-fnct-item-record* t :ok :ok 32 32) :fault)
      (equal (fn2-cns-item-binding-answer :found *fn2-fnct-item-record* t :ok :ok 32 0) :found)))
(defconst *fn2-cfi-profile*
 (put-assoc-equal :cns 1 (put-assoc-equal :control-connections 2
  (put-assoc-equal :extent-slots 128 *fn2-cursor-profile*))))
(defconst *fn2-cfi-mid* "<integrity@example.invalid>")
(defconst *fn2-cfi-headers*
 '("From: a@example.invalid" "Subject: integrity" "Newsgroups: local.test"
   "Message-ID: <integrity@example.invalid>" ""))
(defconst *fn2-cfi-a* (fn2-cw-crlf-octets (append *fn2-cfi-headers* '("body AAA"))))
(defconst *fn2-cfi-b* (fn2-cw-crlf-octets (append *fn2-cfi-headers* '("body BBB"))))
(defun fn2-cfi-find (bytes store)
 (declare (xargs :verify-guards nil))
 (cond ((atom store) nil)
       ((equal (take (len bytes) (cdar store)) bytes) (car store))
       (t (fn2-cfi-find bytes (cdr store)))))
(defun fn2-cfi-cat (frames)
 (declare (xargs :verify-guards nil))
 (if (atom frames) nil (append (car frames) (fn2-cfi-cat (cdr frames)))))
(defun fn2-cfi-lengths (frames)
 (declare (xargs :verify-guards nil))
 (if (atom frames) nil (cons (len (car frames)) (fn2-cfi-lengths (cdr frames)))))
(defun fn2-cfi-case (substitute fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor *fn2-cfi-profile* :echo nil fn2-core))
      (workspace-ok
       (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (ok)
        (let ((class (fn2-cns-lease-class-of fn2-pool)))
         (and (natp class) (< class (fn2-pool-nclasses fn2-pool))
              (<= *fn2-cns-item-workspace-bytes* (fn2-pool-class-sizesi class fn2-pool)))) ok))
      ((mv epoch fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
        (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
      (post (fn2-cw-crlf-octets (append '("POST") *fn2-cfi-headers* '("body AAA" "." "QUIT"))))
      ((mv posted clients store fn2-core)
       (fn2-cw-loop 20000 0 0 (fn2-cw-clients (list (list post (list (len post))))) nil fn2-core))
      (entry (fn2-cfi-find *fn2-cfi-a* store))
      ((unless (and workspace-ok (eq epoch :ok) (eq posted :quiet) entry
                    (equal (fn2-cw-results clients)
                      (list (list (fn2-cw-crlf-octets
                        '("200 fn-nntp experimental server ready" "340 send article to be posted"
                          "240 article received OK" "205 closing connection")) t)))
                    (equal (len *fn2-cfi-a*) (len *fn2-cfi-b*))
                    (not (equal *fn2-cfi-a* *fn2-cfi-b*))))
       (mv (list :setup epoch posted (and entry t)) fn2-core))
      ;; Newest write overlays the raw unit only; all published metadata
      ;; and all bytes outside the selected article remain unchanged.
      (store (if substitute (cons (cons (car entry) *fn2-cfi-b*) store) store))
      ;; MID uses octets without CRLF; the independent protocol encoder
      ;; receives the same named occurrence for both device worlds.
      (frames (list (fnc-fetch (take (length *fn2-cfi-mid*) (fn2-cw-crlf-octets (list *fn2-cfi-mid*))) 1)
                    (fnc-register 1 1) (fnc-read (fnc-issued 1 *fnc-fixture-owner-pid* 1 1 0) 1) (fnc-control 5)))
      (fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
      ((mv admitted fn2-core) (fn2-machine-admit-fn2-ctl 1 78 3 0 fn2-core))
      ((unless (eq admitted :ok)) (mv (list :admit admitted) fn2-core))
      ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
      (fn2-core (fn2-exec-wake wake fn2-core))
      (clients (list (list nil nil nil nil)
                     (list (fn2-cfi-cat frames) (fn2-cfi-lengths frames) nil nil)))
      ((mv status clients & fn2-core) (fn2-cw-loop 40000 0 2 clients store fn2-core))
      (replies (fnc-replies '(fetch register read) (car (nth 1 (fn2-cw-results clients)))))
      (fetch (car replies)) (read (nth 2 replies))
      (item (car (nth 3 (nth 2 read)))))
  (mv (and (eq status :quiet) (not (fn2-core-stopped-p fn2-core))
           (equal (nth 1 replies) '(:accepted "" 0))
           (if substitute
               (and (equal fetch '(:refused "unavailable" nil))
                    (equal read '(:refused "unavailable" nil)))
             (and (equal fetch (list :accepted "" *fn2-cfi-a*))
                  (eq (car read) :accepted) (equal (nth 2 (nth 2 read)) 1)
                  (equal item (list :record 1 *fn2-cfi-mid* *fn2-cfi-a*))))) fn2-core)))
(defun fn2-cfi-run (substitute)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core) (fn2-cfi-case substitute fn2-core) answer)))
(assert-event (equal (fn2-cfi-run nil) t))
(assert-event (equal (fn2-cfi-run t) t))

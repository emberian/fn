; AUTHORED source regressions for the actual input/controller join.
; These are pure-model tests, not candidate source/custody/native qualification.
(in-package "ACL2")
(include-book "../../books/consumer-control-row-cursor")
(include-book "../../books/consumer-configured-control-event")
(include-book "../../books/catalog-record")

(defun ctcdt-line (s) (append (fn-record-string-octets s) '(13 10)))
(defun ctcdt-bytes (lines)
 (if (consp lines) (append (ctcdt-line (car lines)) (ctcdt-bytes (cdr lines)))
   (append '(13 10) (ctcdt-line "body"))))
(defconst *ctcdt-target-bytes*
 (ctcdt-bytes '("From: p@example.invalid" "Newsgroups: fn.mod.a"
                "Message-ID: <t@example.invalid>" "Subject: t")))
(defconst *ctcdt-cancel-bytes*
 (ctcdt-bytes '("From: p@example.invalid" "Date: Wed, 23 Sep 2026 12:00:00 +0000"
                "Newsgroups: control.cancel" "Message-ID: <c@example.invalid>"
                "Subject: cancel" "Control: cancel <t@example.invalid>")))
(defun ctcdt-row (seq txid msgid groups bytes)
 (fn-held-make seq txid txid msgid seq groups "a" "s" "e" 2 0
   (fn-held-facts-of bytes)
   (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0) nil nil))
(defconst *ctcdt-target* (ctcdt-row 0 4 "<t@example.invalid>" '("fn.mod.a") *ctcdt-target-bytes*))
(defconst *ctcdt-cancel* (ctcdt-row 1 5 "<c@example.invalid>" '("control.cancel") *ctcdt-cancel-bytes*))
(defconst *ctcdt-article* (fn-make-article "<c@example.invalid>" nil '("control.cancel") nil t nil))
(defconst *ctcdt-verdict* (fn-stx-make-verdict :verified (make-list 32 :initial-element 17) 1))
(defconst *ctcdt-verdicts* (list (cons "<else@example.invalid>" :unrelated)
                                (cons "<c@example.invalid>" *ctcdt-verdict*)))
(defconst *ctcdt-chain* (fn-ccpx-entry (fn-cfg-empty) 0 0 0 :recorded-genesis nil))
(defconst *ctcdt-start* (fn-ctcd-begin *ctcdt-article* *ctcdt-verdicts* *ctcdt-chain* :captured-source 2 5))
(defconst *ctcdt-skip* (fn-ctcd-row (fn-cp-nth 1 *ctcdt-start*) *ctcdt-target*))
(defconst *ctcdt-selected* (fn-ctcd-row (fn-cp-nth 1 *ctcdt-skip*) *ctcdt-cancel*))
(defconst *ctcdt-vskip* (fn-ctcd-step (fn-cp-nth 1 *ctcdt-selected*)))
(defconst *ctcdt-vselected* (fn-ctcd-step (fn-cp-nth 1 *ctcdt-vskip*)))
(defconst *ctcdt-targetselected* (fn-ctcd-row (fn-cp-nth 1 *ctcdt-vselected*) *ctcdt-target*))
(defconst *ctcdt-finished* (fn-ctcd-step (fn-cp-nth 1 *ctcdt-targetselected*)))

; Actual constructor source must establish the new mandatory held schema;
; this test intentionally fails if inherited fixtures no longer do so.
;@mutation-witness actual-oldest-row-control-phases-complete-plan
(assert-event
 (and (fn-store-event-p *ctcdt-target*) (fn-store-event-p *ctcdt-cancel*)
      (equal (fn-ctcd-step (fn-cp-nth 1 *ctcdt-start*))
             (list :read (fn-cp-nth 1 *ctcdt-start*) 0 :captured-source))
      (equal (fn-cp-nth 4 (fn-cp-nth 1 *ctcdt-skip*)) 1)
      (equal (fn-cp-nth 10 (fn-cp-nth 1 *ctcdt-selected*)) *ctcdt-cancel*)
      (equal (fn-cp-nth 9 (fn-cp-nth 1 *ctcdt-vskip*)) (cdr *ctcdt-verdicts*))
      (equal (fn-cp-nth 12 (fn-cp-nth 1 *ctcdt-vselected*)) *ctcdt-verdict*)
      (equal (fn-cp-nth 4 (fn-cp-nth 1 *ctcdt-vselected*)) 0)
      (equal (fn-cp-nth 0 *ctcdt-finished*) :plan)
      (equal (fn-cp-nth 1 *ctcdt-finished*)
       (fn-ctl-article-plan *ctcdt-article* *ctcdt-verdicts*
                           (list *ctcdt-target* *ctcdt-cancel*) nil))))

;@corrupted-state row-coordinate-mismatch-never-becomes-absence
(assert-event
 (and (equal (fn-cp-nth 0 (fn-ctcd-row (fn-cp-nth 1 *ctcdt-start*) *ctcdt-cancel*)) :unavailable)
      (equal (fn-cp-nth 0 (fn-ctcd-row (fn-cp-nth 1 *ctcdt-start*) nil)) :unavailable)))

; A later same-MID candidate never shadows the oldest completed ordinal.
;@mutation-witness exact-oldest-row-ends-read-before-later-duplicate
(assert-event
 (let* ((a (fn-make-article "<t@example.invalid>" nil '("fn.mod.a") nil t nil))
        (b (fn-ctcd-begin a nil *ctcdt-chain* :captured-source 2 5)))
  (equal (fn-ctcd-row (fn-cp-nth 1 b) *ctcdt-target*)
         (list :plan nil nil (fn-ctl-control-locks
                               (fn-hf-control (fn-held-facts *ctcdt-target*)))))))

; Existing pending withdrawal reports fence when their target arrives,
; even with no old visible article. One resolve/reverse cell preserves order.
;@mutation-witness arriving-target-resolves-saved-locks-and-fences
(assert-event
 (let* ((a (fn-make-article "<t@example.invalid>" nil '("fn.mod.a") nil t nil))
        (w (fn-ctl-withdrawal-make "<t@example.invalid>" "<c@example.invalid>" :p :author 1))
        (s (fn-capr-state nil nil nil nil nil nil nil nil (list w) nil nil 0 0 nil nil nil))
        (job (list :configured-control-event s :saved-physical :saved-produced
                    (list a) nil nil nil nil :append :article nil nil nil nil
                    :preserved *ctcdt-chain* :captured-source 2 5 nil 1))
        (start (fn-cape-article-result job (list :plan nil nil '(76))))
        (resolve (fn-cape-step (fn-cp-nth 1 start)))
        (endws (fn-cape-step (fn-cp-nth 1 resolve)))
        (reverse (fn-cape-step (fn-cp-nth 1 endws)))
        (finish (fn-cape-step (fn-cp-nth 1 reverse)))
        (j (fn-cp-nth 1 finish)))
  (and (equal (fn-cp-nth 2 j) :saved-physical)
       (equal (fn-cp-nth 3 j) :saved-produced)
       (equal (fn-cp-nth 15 j) :changed)
       (equal (fn-cp-nth 13 j) (list (fn-ctl-w-with-tlocks w '(76))))
       (equal (fn-cp-nth 10 j) :finish))))

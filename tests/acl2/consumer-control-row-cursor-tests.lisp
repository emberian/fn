; UNHOOKED cert-roots (2026-10-02): out of the Makefile certify roots -- it depends on the FNCE consumer-authority / remote-consumer event kinds stage 0 reverted from the wire-event grammar (814763fdf; planning/design-store-representation-2026-10-01.md section 4). The code stays; it returns with that grammar.
; AUTHORED source regressions for the actual input/controller join.
; These are pure-model tests, not candidate source/custody/native qualification.
(in-package "ACL2")
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

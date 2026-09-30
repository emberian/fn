(in-package "ACL2")
(include-book "../../books/history-key-cursor")

(defun hkct-run (n source index hash)
 (declare (xargs :verify-guards nil))
 (if (zp n) (mv index hash)
  (mv-let (v index hash) (fn-hkc-tick source index hash)
   (declare (ignore v)) (hkct-run (1- n) source index hash))))

(defconst *hkct-row*
 (fn-held-make 0 1 0 "<a@x>" 0 '("fn.test") "o" "s" "e" 1 5
               (fn-hf-make 100 14 2 nil)
               (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0)
               nil nil))

(assert-event
 (let ((source "<a@x>") (salt 7))
  (and (unsigned-byte-p 32 salt)
       (equal (fn-hist-fnv source 0 (fn-hkc-begin salt))
              (fn-hist-hash source salt)))))
(assert-event
 (let ((source "<a@x>") (index 0) (hash (fn-hkc-begin 7)) (octet 60))
  (and (stringp source) (natp index) (< index (length source))
       (unsigned-byte-p 32 hash) (equal octet (char-code (char source index)))
       (equal (fn-hist-fnv source (+ 1 index) (fn-hkc-byte octet hash))
              (fn-hist-fnv source index hash)))))
; Source-byte misattribution: all remaining residual premises hold.
(assert-event
 (let ((source "<a@x>") (index 0) (hash (fn-hkc-begin 7)) (octet 61))
  (and (stringp source) (natp index) (< index (length source))
       (unsigned-byte-p 32 hash) (not (equal octet (char-code (char source index))))
       (not (equal (fn-hist-fnv source (+ 1 index) (fn-hkc-byte octet hash))
                   (fn-hist-fnv source index hash))))))
(assert-event
 (let* ((source (fn-hist-key-msgid *hkct-row*)) (salt 7)
        (r (mv-list 2 (hkct-run (length source) source 0 (fn-hkc-begin salt))))
        (index (car r)) (hash (cadr r))
        (step (mv-list 3 (fn-hkc-tick source index hash))))
  (and (equal source (fn-hist-key-msgid *hkct-row*)) (stringp source)
       (natp index) (unsigned-byte-p 32 hash)
       (equal (fn-hist-fnv source index hash) (fn-hist-hash source salt))
       (equal (car step) :done)
       (equal (fn-hkc-result (nth 2 step)) (fn-hp-mkey *hkct-row* salt)))))
(assert-event
 (let* ((source "<a@x>") (index 0) (hash (fn-hkc-begin 7))
        (r (mv-list 3 (fn-hkc-tick source index hash))))
  (and (stringp source) (natp index) (equal (car r) :continue)
       (equal (nth 1 r) (+ 1 index))
       (< (nfix (- (length source) (nth 1 r))) (nfix (- (length source) index)))
       (unsigned-byte-p 32 hash) (natp (nth 1 r))
       (unsigned-byte-p 32 (nth 2 r)))))
; Empty string is a real terminal; its salted basis remains the hash.
(assert-event
 (equal (mv-list 3 (fn-hkc-tick "" 0 (fn-hkc-begin 7)))
        (list :done 0 (fn-hkc-begin 7))))

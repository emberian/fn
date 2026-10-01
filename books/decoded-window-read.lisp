; Exact scalar publication of a physically returned stored window.
(in-package "ACL2")
(include-book "page-window-executor")
(include-book "decoded-window-begin")

(defun fn-pwz-plan-matches-token (z token)
  (declare (xargs :guard (and (true-listp z) (true-listp (nth 1 z)))
                  :guard-hints (("Goal" :in-theory (enable fn-pwz-tokenp)))))
  (let ((s (nth 1 z)))
    (and (fn-pwz-tokenp token)
         (equal (nth 8 s) (fn-pwz-nth 1 token))
         (equal (nth 10 s) token)
         (equal (list (nth 1 s) (nth 2 s) (nth 3 s) (nth 11 s) (nth 12 s)
                      (nth 3 z) (nth 6 s) (nth 2 z) (fn-pwz-nth 10 token))
                (cddr token))
         (equal (nth 13 s) (nth 12 s))
         (equal (nth 5 s) 0)
         (equal (nth 4 z) (min 16384 (nfix (- (nfix (nth 2 z)) (nfix (nth 3 z)))))))))

(local
 (defthm fn-pwz-nth-is-nth-by-definition
   (implies (natp i) (equal (fn-pwz-nth i fields) (nth i fields)))
   :hints (("Goal" :in-theory (enable fn-pwz-nth)))))

(local
 (defthm fn-pwz-nine-naturals-shape
   (implies (fn-pwz-naturals 9 fields)
            (and (natp (nth 0 fields)) (natp (nth 1 fields)) (natp (nth 2 fields)) (natp (nth 3 fields)) (natp (nth 4 fields)) (natp (nth 5 fields)) (natp (nth 6 fields)) (natp (nth 7 fields)) (natp (nth 8 fields))
                 (equal fields (list (nth 0 fields) (nth 1 fields) (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields) (nth 7 fields) (nth 8 fields)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :expand ((fn-pwz-naturals 9 fields) (fn-pwz-naturals 8 (cdr fields)) (fn-pwz-naturals 7 (cdr (cdr fields))) (fn-pwz-naturals 6 (cdr (cdr (cdr fields)))) (fn-pwz-naturals 5 (cdr (cdr (cdr (cdr fields))))) (fn-pwz-naturals 4 (cdr (cdr (cdr (cdr (cdr fields)))))) (fn-pwz-naturals 3 (cdr (cdr (cdr (cdr (cdr (cdr fields))))))) (fn-pwz-naturals 2 (cdr (cdr (cdr (cdr (cdr (cdr (cdr fields)))))))) (fn-pwz-naturals 1 (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr fields))))))))) (fn-pwz-naturals 0 (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr fields)))))))))))
           :in-theory (enable fn-pwz-naturals)))))

(defthm fn-pwz-begin-captures-typed-request
  (implies (fn-pwz-tokenp token)
           (fn-pwz-plan-matches-token
             (mv-nth 0 (fn-pwz-begin token incarnation pgs-digest-state
                         fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)) token))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pwz-nine-naturals-shape (fields (cddr token))))
           :in-theory (e/d (fn-pwz-plan-matches-token fn-pwz-begin fn-pwz-tokenp
                              fn-pwz-descriptorp fn-ewz-begin fn-ewz-state fn-ews-begin fn-ewp-begin fn-ewp-state)
                             (fn-pwz-naturals fn-pwz-nth fn-pwz-dictionary fn-pzw-initialize fn-pzd-budget pgs-dcb-begin)))))

(defun fn-pwz-outcome (ledger worker token z)
  (declare (xargs :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (cond ((fn-pwx-boundp ledger worker token :cancelled-returned) :cancelled)
        ((not (fn-pwx-boundp ledger worker token :returned)) :stale-job)
        ((not (fn-pwz-plan-matches-token z token)) '(:fault :state))
        ((fn-ewz-publication z) :ready)
        (t (list :fault (nth 0 z) (nth 0 (nth 1 z)) (nth 8 z)))))

(defun fn-pwz-byte (ledger worker token z i fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer
                  :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (let ((outcome (fn-pwz-outcome ledger worker token z)))
    (if (not (eq outcome :ready)) (mv outcome nil)
      (if (and (natp i) (natp (nth 4 z)) (<= (nth 4 z) 16384) (< i (nth 4 z)))
          (mv :byte (fn-ew-bytesi i fn-ew-buffer))
        (mv :unavailable nil)))))

; All physical/codec coordinates remain checked by the core. DICT-ID is
; the immutable shipped ID selected at initial captured request discovery.
(defun fn-pwz-byte-at (ledger worker token z file eoff elen poff compressed trailer decoded dict-id i fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer
                  :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (let ((outcome (fn-pwz-outcome ledger worker token z)))
    (if (not (eq outcome :ready)) (mv outcome nil)
      (if (and (equal (list file eoff elen poff compressed trailer decoded dict-id)
                     (list (fn-pwz-nth 2 token) (fn-pwz-nth 3 token) (fn-pwz-nth 4 token)
                           (fn-pwz-nth 5 token) (fn-pwz-nth 6 token) (fn-pwz-nth 8 token)
                           (fn-pwz-nth 9 token) (fn-pwz-nth 10 token)))
               (natp i) (natp decoded) (< i decoded)
               (natp (fn-pwz-nth 7 token)) (<= (fn-pwz-nth 7 token) i))
          (fn-pwz-byte ledger worker token z (- i (fn-pwz-nth 7 token)) fn-ew-buffer)
        (mv :unavailable nil)))))

(in-theory (disable fn-pwz-plan-matches-token fn-pwz-outcome fn-pwz-byte fn-pwz-byte-at))

; Shared LC locator-only MOVE effect, used by cleaning and cold replay.
(in-package "ACL2")
(include-book "catalog-columns-guards")
(include-book "log-checkpoint-total-accessors")

(defun fn-lc-move-sequence (move)
 (declare (xargs :guard t)) (fn-lc-at 1 move))

(defun fn-lc-move-loc0 (move)
 (declare (xargs :guard t)) (fn-lc-at 2 move))

(defun fn-lc-move-loc1 (move)
 (declare (xargs :guard t))
 (+ (* (nfix (fn-lc-at 3 (fn-lc-at 4 move))) 4294967296)
       (nfix (fn-lc-at 4 (fn-lc-at 4 move)))))

(defun fn-lc-move-packet (move)
 (declare (xargs :guard t))
 (list nil (fn-lc-at 3 move) (fn-lc-at 4 move)))

(defun fn-lc-read-suf (loc0 loc1 segs)
 (declare (xargs :guard t))
 ; The current LB format's complete suffix is its typed home frame.
 (ec-call (fn-lc-read-home-frame (ec-call (fn-lc-home-position loc0 loc1)) segs)))

(defun fn-lc-replay-move (move fn-lbc)
 (declare (xargs :stobjs fn-lbc
   :guard (and (fn-lbc-p fn-lbc) (natp (fn-lc-move-sequence move))
               (< (fn-lc-move-sequence move) (fn-lc-count fn-lbc))
               (fn-locp (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)))
   :verify-guards nil))
 (let* ((fn-lbc (update-fn-lbc-loc0 (fn-lc-move-sequence move)
                                      (fn-lc-move-loc0 move) fn-lbc))
        (fn-lbc (update-fn-lbc-loc1 (fn-lc-move-sequence move)
                                      (fn-lc-move-loc1 move) fn-lbc)))
   fn-lbc))

(local (defthm lcm-count-of-loc0
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-count (update-fn-lbc-loc0 i word fn-lbc))
         (fn-lbc-count fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
     '((:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
       (:DEFINITION FN-LBC-COUNT)
       (:DEFINITION FN-LBC-ROW-STORE)
       (:DEFINITION NATP)
       (:DEFINITION NTH)
       (:DEFINITION UPDATE-FN-LBC-LOC0)
       (:DEFINITION UPDATE-FN-LBC-ROW-STORE)
       (:EXECUTABLE-COUNTERPART EQUAL)
       (:EXECUTABLE-COUNTERPART FN-DM-ZEROSP)
       (:EXECUTABLE-COUNTERPART LEN)
       (:EXECUTABLE-COUNTERPART NFIX)
       (:EXECUTABLE-COUNTERPART ZP)
       (:REWRITE FN-DM-LEN-UPDATE-NTH)
       (:REWRITE FN-DM-NTH-OF-ZEROS)
       (:REWRITE FN-DM-NTH-UPDATE-NTH)
       (:REWRITE FN-LBC-ROWWORDS-COUNT-IS-LEN)
       (:REWRITE FN-LBC-ROWWORDS-SET-LOC0-IS-UPDATE-NTH)
       (:REWRITE FN-MPXL-LEN-UPDATE-NTH)
       (:REWRITE PGS-X-NFIX-WHEN-NATP)))))))

(verify-guards fn-lc-replay-move
 :hints (("Goal" :in-theory (e/d (fn-lc-count fn-locp)
  (fn-lbc-p fn-lbc-count update-fn-lbc-loc0 fn-lc-move-sequence
   fn-lc-move-loc0 fn-lc-move-loc1)))))

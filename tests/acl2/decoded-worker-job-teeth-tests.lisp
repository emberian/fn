; Critical scalar-publication witness: run the real decode before retiring.
(in-package "ACL2")
(include-book "decoded-worker-reuse-execution-tests")
(include-book "../../books/defkeystone")
; A congruent local name matches the unchanged theorem's logical JOB variable.
(defstobj job
  (dwjt-carry :type fn-pww-carry)
  (dwjt-input :type fn-octets)
  (dwjt-hash :type pgs-digest-state)
  (dwjt-zin :type fn-zin-st)
  (dwjt-win :type fn-zin-win)
  (dwjt-tab :type fn-zin-tab)
  (dwjt-out :type fn-zin-out)
  (dwjt-window :type fn-ew-buffer)
  :congruent-to fn-decoded-job :inline t)

(defconst *dwjt-compressed* '(1 1 0 254 255 90))
(defconst *dwjt-message* (append '(9 8) *dwjt-compressed* '(7)))
(defconst *dwjt-digest* (fn-blake3 *dwjt-message*))
(defconst *dwjt-trailer* (fn-bch-pack *dwjt-digest*))
(defconst *dwjt-archive* (append *dwjt-message* *dwjt-digest*))
(defconst *dwjt-admit*
  (mv-list 3
    (fn-pwz-admit
      (nth 1 (mv-list 2 (fn-prl-register (fn-prl-make '(200000 0 2 1 20)) 7 '(64 0 1 0 0))))
      (list 7 100 (len *dwjt-message*) 102 (len *dwjt-compressed*) 0 *dwjt-trailer* 1 0)
      '(86928 0 0 1 1))))
(defconst *dwjt-token* (nth 1 *dwjt-admit*))
(defconst *dwjt-acquired* (mv-list 3 (fn-pwx-acquire (nth 2 *dwjt-admit*) (fn-pxe-new 0) *dwjt-token*)))
(defconst *dwjt-returned*
  (mv-list 3 (fn-pwx-return (nth 2 *dwjt-acquired*) (nth 1 *dwjt-acquired*) *dwjt-token*)))
(defun dwjt-build (job)
  (declare (xargs :stobjs job :verify-guards nil))
  (let ((job (fn-dwj-reserve job)))
    (mv-let (assigned job)
      (fn-dwj-assign (nth 2 *dwjt-acquired*) (nth 1 *dwjt-acquired*) *dwjt-token* *dwjt-token* 47 job)
      (declare (ignore assigned))
      (mv-let (begun job) (fn-dwj-begin *dwjt-token* job)
        (declare (ignore begun))
        (mv-let (terminal job) (dwret-drive 10000 *dwjt-archive* *dwjt-token* job)
          (declare (ignore terminal)) job)))))
(defun dwjt-retire-check (ledger worker token job)
  (declare (xargs :stobjs job :verify-guards nil))
  (mv-let (word job) (fn-dwj-retire ledger worker token job)
    (mv (equal word :reusable) job)))
(defun dwjt-retired-byte-check (ledger worker token query-ledger query-worker query-token
                               file eoff elen poff compressed trailer decoded dict-id i job)
  (declare (xargs :stobjs job :verify-guards nil))
  (mv-let (word job) (fn-dwj-retire ledger worker token job)
    (declare (ignore word))
    (mv-let (byte-word byte)
      (fn-dwj-byte-at query-ledger query-worker query-token file eoff elen poff compressed
                      trailer decoded dict-id i job)
      (declare (ignore byte))
      (mv (equal byte-word :byte) job))))

(defun dwjt-byte-check (query-ledger query-worker query-token file eoff elen poff compressed trailer decoded dict-id i job)
  (declare (xargs :stobjs job :verify-guards nil))
  (mv-let (word byte) (fn-dwj-byte-at query-ledger query-worker query-token file eoff elen poff compressed trailer decoded dict-id i job)
    (declare (ignore byte)) (mv (equal word :byte) job)))

; fn-owner-page-decoded-job-retire in host/page-decoded-window-host.lisp; host path:
; tests/test_native_decoded_custody.py::
; test_held_decoded_read_allows_post_then_cancel_return_release_and_reopen.
(defun dwjt-not-retired-byte-check (ledger worker token query-ledger query-worker query-token file eoff elen poff compressed trailer decoded dict-id i job)
  (declare (xargs :stobjs job :verify-guards nil))
  (mv-let (word job) (dwjt-retired-byte-check ledger worker token query-ledger query-worker query-token
                             file eoff elen poff compressed trailer decoded dict-id i job) (mv (not word) job)))

(defun dwjt-not-byte-check (query-ledger query-worker query-token file eoff elen poff compressed trailer decoded dict-id i job)
  (declare (xargs :stobjs job :verify-guards nil))
  (mv-let (word job) (dwjt-byte-check query-ledger query-worker query-token file eoff elen poff compressed trailer decoded dict-id i job) (mv (not word) job)))

(defteeth fn-dwj-retired-job-refuses-scalar-publication
  :claim (((reusable (equal (mv-nth 0 (fn-dwj-retire ledger worker token job)) :reusable)))
          (not (equal (mv-nth 0
             (fn-dwj-byte-at query-ledger query-worker query-token file eoff elen poff compressed
                             trailer decoded dict-id i
                             (mv-nth 1 (fn-dwj-retire ledger worker token job))))
           :byte)))
  :subject fn-dwj-retire
  :witness ((ledger (nth 2 *dwjt-returned*)) (worker (nth 1 *dwjt-returned*)) (token *dwjt-token*)
            (query-ledger (nth 2 *dwjt-returned*)) (query-worker (nth 1 *dwjt-returned*))
            (query-token *dwjt-token*) (file 7) (eoff 100) (elen (len *dwjt-message*))
            (poff 102) (compressed (len *dwjt-compressed*)) (trailer *dwjt-trailer*)
            (decoded 1) (dict-id 0) (i 0))
  :stobjs ((job (dwjt-build job)))
  :stobj-checks
  (((equal (mv-nth 0 (fn-dwj-retire ledger worker token job)) :reusable)
    (dwjt-retire-check ledger worker token job)
    :hints (("Goal" :in-theory (e/d (dwjt-retire-check) (fn-dwj-retire)))))
   ((equal (mv-nth 0
           (fn-dwj-byte-at query-ledger query-worker query-token file eoff elen poff compressed
                           trailer decoded dict-id i
                           (mv-nth 1 (fn-dwj-retire ledger worker token job)))) :byte)
    (dwjt-retired-byte-check ledger worker token query-ledger query-worker query-token
                             file eoff elen poff compressed trailer decoded dict-id i job)
    :hints (("Goal" :in-theory (e/d (dwjt-retired-byte-check) (fn-dwj-retire fn-dwj-byte-at)))))
   ((equal (mv-nth 0 (fn-dwj-byte-at query-ledger query-worker query-token file eoff elen poff compressed trailer decoded dict-id i job)) :byte)
    (dwjt-byte-check query-ledger query-worker query-token file eoff elen poff compressed trailer decoded dict-id i job)
    :hints (("Goal" :in-theory (e/d (dwjt-byte-check) (fn-dwj-byte-at)))))
 ((not (equal (mv-nth 0
           (fn-dwj-byte-at query-ledger query-worker query-token file eoff elen poff compressed
                           trailer decoded dict-id i
                           (mv-nth 1 (fn-dwj-retire ledger worker token job)))) :byte))
 (dwjt-not-retired-byte-check ledger worker token query-ledger query-worker query-token file eoff elen poff compressed trailer decoded dict-id i job)
 :hints (("Goal" :in-theory (e/d (dwjt-not-retired-byte-check dwjt-retired-byte-check) (fn-dwj-byte-at fn-dwj-retire)))))
 ((not (equal (mv-nth 0 (fn-dwj-byte-at query-ledger query-worker query-token file eoff elen poff compressed trailer decoded dict-id i job)) :byte))
 (dwjt-not-byte-check query-ledger query-worker query-token file eoff elen poff compressed trailer decoded dict-id i job)
 :hints (("Goal" :in-theory (e/d (dwjt-not-byte-check dwjt-byte-check) (fn-dwj-byte-at fn-dwj-retire))))))
  :breaks ((reusable ((ledger (nth 2 *dwjt-acquired*)) (worker (nth 1 *dwjt-acquired*)))))
  :mutations ((retirement-skipped
               (:conclusion
                (not (equal (mv-nth 0
                       (fn-dwj-byte-at query-ledger query-worker query-token file eoff elen poff compressed
                                       trailer decoded dict-id i job)) :byte)))
               () :fault "the scalar reader uses the decoded job before the retirement transition")))

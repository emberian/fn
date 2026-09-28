; fn: teeth for books/history-pages-owner.lisp (lane arena-store-5,
; 2026-09-28, m3c P1's link).
;
; What this book is evidence FOR.  The witness is owner-checkpoint-open-
; tests' reachable owner: two retention events and two configuration
; records, the checkpoint the capture of the first event, the log suffix
; the second.  (1) fn-hpo-installed-records-are-checkpoint-then-suffix:
; the host's open (fn-rii-sco-extend-open) and the owner's install
; (fn-ock-install) give an owner, not :fault, whose store holds the
; checkpoint's record then the suffix's.  (2) fn-hpo-records-at-is-installed-nth:
; the image written from the checkpoint's records (fn-hp-x-init then
; fn-hp-x-append-all) answers both of the installed owner's records --
; the first from the image, the second from the suffix -- and refuses the
; third.  (3) fn-hpo-records-at-is-nth-of-extension: a later store with a
; third record, read through the same image and the suffix since it.
; (4) fn-hpo-snapshot-image-is-next-checkpoint: appending the suffix to
; the image leaves the image of the next checkpoint's records.  Each
; positive witness asserts the complete antecedent and conclusion; each
; characteristic hypothesis has a removal witness (the retained ones hold,
; the omitted one fails, the conclusion fails) and a must-fail-checked of
; the weakened statement.
(in-package "ACL2")
(include-book "../../books/history-pages-owner")
(include-book "must-fail-checked")

(local (in-theory (enable fn-hp-vhold-is-x)))

(defconst *hpo-events*
  (list (fn-store-retention-event-make :undertake 0 0 0 "forward-ock" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1 "forward-ock" "subject" "evidence" 0)))
(defconst *hpo-e0* (car *hpo-events*))
(defconst *hpo-e1* (cadr *hpo-events*))
(defconst *hpo-e2* (fn-store-retention-event-make :undertake 2 2 2 "forward-ock" "other" "evidence" 5))
(defconst *hpo-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))
(defconst *hpo-c* (fn-sco-capture *hpo-configs* (list *hpo-e0*)))
(defconst *hpo-suffix* (list *hpo-e1*))

(defmacro hpo-oc (c configs suffix frontier)
  ; the owner the host installs: the open's pair, then fn-ock-install
  `(let ((pair (fn-rii-sco-extend-open ,c ,configs ,suffix ,frontier)))
     (fn-ock-install (car (cadr pair)) (cadr (cadr pair)) 4)))
(defmacro hpo-records (oc) `(fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner ,oc)))))

(defconst *hpo-m0* '(nil nil nil nil nil nil))   ; the empty page store
(defconst *hpo-e* '(0 0 0 0 0))
(defconst *hpo-s1* '(1 1 1 1 1))
(defmacro hpo-image (evs)
  ; the image of EVS from the empty store: (mv V K N LENS STARTS NP MEM)
  `(fn-hp-x-append-all ,evs 0 0 0 *hpo-e* *hpo-s1* 1 (mv-nth 5 (fn-hp-x-init *hpo-m0*))))

; -----------------------------------------------------------------------------
; (1) KEYSTONE fn-hpo-installed-records-are-checkpoint-then-suffix.
(defthm hpo-installed-w
  (let ((oc (hpo-oc *hpo-c* *hpo-configs* *hpo-suffix* 8)))
    (and (not (equal oc :fault))
         (equal (hpo-records oc) (append (true-list-fix (fn-sco-records *hpo-c*)) *hpo-suffix*))
         (equal (hpo-records oc) *hpo-events*)))
  :rule-classes nil)

;; Without the install's success: no configuration history, the install
;; refuses (:fault) and the "owner" holds no records.
(defthm hpo-installed-removal
  (let ((oc (hpo-oc *hpo-c* nil *hpo-suffix* 8)))
    (and (equal oc :fault)
         (not (equal (hpo-records oc) (append (true-list-fix (fn-sco-records *hpo-c*)) *hpo-suffix*)))))
  :rule-classes nil)
(must-fail-checked
 (defthm hpo-installed-without-success
   ; the keystone's conclusion without its hypothesis, at the witness's
   ; checkpoint and suffix, for every configuration history
   (let* ((pair (fn-rii-sco-extend-open *hpo-c* configs *hpo-suffix* 8))
          (oc (fn-ock-install (car (cadr pair)) (cadr (cadr pair)) 4)))
     (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
            *hpo-events*))
   :hints (("Goal" :in-theory (disable fn-rii-sco-extend-open fn-ock-install)))))

; -----------------------------------------------------------------------------
; (2) KEYSTONE fn-hpo-records-at-is-installed-nth.
(defthm hpo-records-at-installed-w
  (let* ((oc (hpo-oc *hpo-c* *hpo-configs* *hpo-suffix* 8))
         (records (hpo-records oc))
         (h (fn-sco-records *hpo-c*))
         (img (hpo-image h))
         (lens (mv-nth 3 img)) (starts (mv-nth 4 img)) (np (mv-nth 5 img)) (mem (mv-nth 6 img)))
    (and (equal (mv-nth 0 img) :ok)
         ; the antecedent
         (not (equal oc :fault))
         (fn-hp-okp h 0) (equal 1 (len h)) (equal lens (fn-hp-lens h 0))
         (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 starts np))
         ; the conclusion at every index: the image's record, the suffix's, past the end
         (equal (len records) 2)
         (equal (fn-hp-records-at 0 1 *hpo-suffix* 0 lens starts mem) (list :ok (list :ok (nth 0 records))))
         (equal (fn-hp-records-at 1 1 *hpo-suffix* 0 lens starts mem) (list :ok (list :ok (nth 1 records))))
         (equal (fn-hp-records-at 2 1 *hpo-suffix* 0 lens starts mem) (list :ok '(:refused :seq)))))
  :rule-classes nil)

;; Without the image hold: the store holds the image of another history (the
;; suffix's event); every other hypothesis holds of the checkpoint's H, and
;; record 0 answers the wrong event.
(defthm hpo-records-at-installed-vhold-removal
  (let* ((oc (hpo-oc *hpo-c* *hpo-configs* *hpo-suffix* 8))
         (records (hpo-records oc))
         (h (fn-sco-records *hpo-c*))
         (img (hpo-image (list *hpo-e1*)))
         (lens (fn-hp-lens h 0)) (starts (mv-nth 4 img)) (np (mv-nth 5 img)) (mem (mv-nth 6 img)))
    (and (not (equal oc :fault))
         (fn-hp-okp h 0) (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
         (not (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 starts np)))
         (equal (mv-nth 0 (fn-hp-records-at 0 1 *hpo-suffix* 0 lens starts mem)) :ok)
         (not (equal (mv-nth 1 (fn-hp-records-at 0 1 *hpo-suffix* 0 lens starts mem))
                     (list :ok (nth 0 records))))))
  :rule-classes nil)
(must-fail-checked
 (defthm hpo-records-at-installed-without-vhold
   (let* ((pair (fn-rii-sco-extend-open c configs suffix frontier))
          (oc (fn-ock-install (car (cadr pair)) (cadr (cadr pair)) max-conns))
          (records (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
          (h (fn-sco-records c))
          (res (fn-hp-records-at i n suffix salt lens starts pgs-mem)))
     (implies (and (not (equal oc :fault))
                   (fn-hp-okp h salt) (equal n (len h)) (equal lens (fn-hp-lens h salt))
                   (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
                   (natp i) (< i (len records)) (equal (mv-nth 0 res) :ok))
              (equal (mv-nth 1 res) (list :ok (nth i records)))))
   :hints (("Goal" :in-theory (disable fn-rii-sco-extend-open fn-ock-install fn-hp-records-at fn-hp-okp
                                       fn-hp-lens fn-hp-starts-okp adt-placement-ok))))
 :step-limit 30000)

;; Without N = (len H): N = 2 reads the suffix's record from the image,
;; which has one row; the answer is not the installed owner's record 1.
(defthm hpo-records-at-installed-n-removal
  (let* ((oc (hpo-oc *hpo-c* *hpo-configs* *hpo-suffix* 8))
         (records (hpo-records oc))
         (h (fn-sco-records *hpo-c*))
         (img (hpo-image h))
         (lens (mv-nth 3 img)) (starts (mv-nth 4 img)) (np (mv-nth 5 img)) (mem (mv-nth 6 img)))
    (and (not (equal oc :fault)) (fn-hp-okp h 0) (equal lens (fn-hp-lens h 0))
         (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 starts np))
         (not (equal 2 (len h)))
         (not (equal (fn-hp-records-at 1 2 *hpo-suffix* 0 lens starts mem)
                     (list :ok (list :ok (nth 1 records)))))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; (3) KEYSTONE fn-hpo-records-at-is-nth-of-extension: a later store with a
; third record; the suffix since H is (nthcdr 1 R).
(defconst *hpo-r3* (list *hpo-e0* *hpo-e1* *hpo-e2*))
(defthm hpo-extension-w
  (let* ((h (list *hpo-e0*)) (r *hpo-r3*)
         (img (hpo-image h))
         (lens (mv-nth 3 img)) (starts (mv-nth 4 img)) (np (mv-nth 5 img)) (mem (mv-nth 6 img))
         (sfx (nthcdr (len h) r)))
    (and (fn-sf-prefixp h r) (fn-hp-okp h 0) (equal lens (fn-hp-lens h 0))
         (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 starts np))
         (equal (fn-hp-records-at 0 1 sfx 0 lens starts mem) (list :ok (list :ok (nth 0 r))))
         (equal (fn-hp-records-at 1 1 sfx 0 lens starts mem) (list :ok (list :ok (nth 1 r))))
         (equal (fn-hp-records-at 2 1 sfx 0 lens starts mem) (list :ok (list :ok (nth 2 r))))
         (equal (fn-hp-records-at 3 1 sfx 0 lens starts mem) (list :ok '(:refused :seq)))))
  :rule-classes nil)

;; Without the prefix: R begins with another event; record 0 answers H's.
(defthm hpo-extension-prefix-removal
  (let* ((h (list *hpo-e0*)) (r (list *hpo-e1* *hpo-e0*))
         (img (hpo-image h))
         (lens (mv-nth 3 img)) (starts (mv-nth 4 img)) (np (mv-nth 5 img)) (mem (mv-nth 6 img)))
    (and (not (fn-sf-prefixp h r)) (fn-hp-okp h 0) (equal lens (fn-hp-lens h 0))
         (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 starts np))
         (equal (mv-nth 0 (fn-hp-records-at 0 1 (nthcdr 1 r) 0 lens starts mem)) :ok)
         (not (equal (mv-nth 1 (fn-hp-records-at 0 1 (nthcdr 1 r) 0 lens starts mem))
                     (list :ok (nth 0 r))))))
  :rule-classes nil)
(must-fail-checked
 (defthm hpo-extension-without-prefix
   (let ((res (fn-hp-records-at i (len h) (nthcdr (len h) r) salt lens starts pgs-mem)))
     (implies (and (fn-hp-okp h salt) (equal lens (fn-hp-lens h salt))
                   (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
                   (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                   (natp i) (< i (len r)) (equal (mv-nth 0 res) :ok))
              (equal (mv-nth 1 res) (list :ok (nth i r)))))
   :hints (("Goal" :in-theory (disable fn-hp-records-at fn-hp-okp fn-hp-lens fn-hp-starts-okp adt-placement-ok
                                       fn-hp-vhold fn-hp-vhold-is-x fn-hp-piw))))
 :step-limit 30000)

; -----------------------------------------------------------------------------
; (4) KEYSTONE fn-hpo-snapshot-image-is-next-checkpoint: base = the
; checkpoint (H = its one record), R = the installed owner's records.
(defthm hpo-snapshot-w
  (let* ((h (fn-sco-records *hpo-c*)) (r *hpo-events*)
         (img (hpo-image h))
         (lens (mv-nth 3 img)) (starts (mv-nth 4 img)) (np (mv-nth 5 img)) (mem (mv-nth 6 img))
         (res (fn-hp-x-append-all (nthcdr (len h) r) 0 0 (len h) lens starts np mem))
         (next (fn-ock-next-checkpoint *hpo-c* *hpo-configs* r)))
    (and (true-listp r) (fn-ock-prefixp h r) (fn-hp-okp h 0) (equal lens (fn-hp-lens h 0))
         (fn-hp-starts-okp starts)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 starts np))
         (equal (mv-nth 0 res) :ok)
         (equal (fn-sco-records next) r)
         (fn-hp-okp r 0)
         (equal (mv-nth 2 res) (len r))
         (equal (mv-nth 3 res) (fn-hp-lens r 0))
         (fn-hp-starts-okp (mv-nth 4 res))
         (fn-hp-vhold 0 (pgs-v-length (mv-nth 6 res)) (mv-nth 6 res) (fn-hp-piw r 0 (mv-nth 4 res) (mv-nth 5 res)))
         ; and the next open reads it: the snapshot's image answers the next checkpoint's records
         (equal (mv-nth 1 (fn-hp-records-at 1 2 nil 0 (mv-nth 3 res) (mv-nth 4 res) (mv-nth 6 res)))
                (list :ok *hpo-e1*))))
  :rule-classes nil)

;; Without the prefix: R does not extend H; the next checkpoint is R's
;; capture but the appended image holds H followed by R's tail, not R.
(defthm hpo-snapshot-prefix-removal
  (let* ((h (fn-sco-records *hpo-c*)) (r (list *hpo-e1* *hpo-e1*))
         (img (hpo-image h))
         (lens (mv-nth 3 img)) (starts (mv-nth 4 img)) (np (mv-nth 5 img)) (mem (mv-nth 6 img))
         (res (fn-hp-x-append-all (nthcdr (len h) r) 0 0 (len h) lens starts np mem)))
    (and (true-listp r) (not (fn-ock-prefixp h r)) (fn-hp-okp h 0) (equal lens (fn-hp-lens h 0))
         (fn-hp-starts-okp starts)
         (fn-hp-vhold 0 (pgs-v-length mem) mem (fn-hp-piw h 0 starts np))
         (equal (mv-nth 0 res) :ok)
         (not (fn-hp-vhold 0 (pgs-v-length (mv-nth 6 res)) (mv-nth 6 res)
                           (fn-hp-piw r 0 (mv-nth 4 res) (mv-nth 5 res))))))
  :rule-classes nil)
(must-fail-checked
 (defthm hpo-snapshot-without-prefix
   (let* ((h (fn-sco-records base))
          (res (fn-hp-x-append-all (nthcdr (len h) r) 0 salt (len h) lens starts np pgs-mem)))
     (implies (and (true-listp r) (fn-hp-okp h salt) (equal lens (fn-hp-lens h salt))
                   (fn-hp-starts-okp starts)
                   (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                   (equal (mv-nth 0 res) :ok))
              (fn-hp-vhold 0 (pgs-v-length (mv-nth 6 res)) (mv-nth 6 res)
                           (fn-hp-piw r salt (mv-nth 4 res) (mv-nth 5 res)))))
   :hints (("Goal" :in-theory (disable fn-hp-x-append-all fn-hp-okp fn-hp-lens fn-hp-starts-okp
                                       fn-hp-vhold fn-hp-vhold-is-x fn-hp-piw fn-sco-records))))
 :step-limit 30000)

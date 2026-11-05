; Served authority's fixtures (docs/design/AUTHORITY-20261105.md section 6),
; over the real assembled core. This book grows with the lane, one witness
; per landed step; the witnesses the ruling names and this book does not yet
; carry are owed (docs/e-surface.md, the authority seam).
;
; fn2-authority-genesis-positive (the store's two persisted principals, the
; first half of fn2-authority-local-binding-positive): store genesis names
; "anonymous" (account slot 0) and "owner" (the profile's :owner-account) in
; fn2-principals with distinct positive durable ids, slot * 2^32 + 1; the
; exact lookup answers each; an unnamed principal, "mini" before its
; principal-create, is :absent; a second boot names the same ids (the ids are
; functions of the profile, never of boot order); and a profile with no owner
; slot below the system row names "anonymous" only. Its controls: a lookup
; of a name one octet longer and one shorter than "owner" is :absent.
(in-package "ACL2")
(include-book "../books/assembly")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-as-profile*
 (put-assoc-equal :owner-account 2
  (put-assoc-equal :identity-arena-bytes 4096
   (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (16 . 4096)) *fn2-profile-tiny*))))
(defun fn2-as-write (bytes slot gen off fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (atom bytes) (mv :ok fn2-core)
  (mv-let (code fn2-core) (fn2-core-write slot gen off (car bytes) 5 1 1 fn2-core)
   (if (eq code :ok) (fn2-as-write (cdr bytes) slot gen (+ 1 off) fn2-core) (mv code fn2-core)))))
(defun fn2-as-chars (cs) (declare (xargs :verify-guards nil)) (if (atom cs) nil (cons (char-code (car cs)) (fn2-as-chars (cdr cs)))))
(defun fn2-as-drive (fuel tx slot gen len fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel 0 fn2-core)
  (mv-let (code p fn2-core) (fn2-principal-lookup tx slot gen 0 len 5 1 1 4096 fn2-core)
   (if (eq code :more) (fn2-as-drive (- fuel 1) tx slot gen len fn2-core) (mv code p fn2-core)))))
(defun fn2-as-lookup (name fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv & slot gen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      (octets (fn2-as-chars (coerce name 'list)))
      ((mv & fn2-core) (fn2-as-write octets slot gen 0 fn2-core))
      ((mv code p fn2-core) (fn2-as-drive 20 0 slot gen (len octets) fn2-core))
      ((mv & fn2-core) (fn2-core-release slot gen 5 1 1 fn2-core)))
  (mv (list code p) fn2-core)))
(defun fn2-as-genesis-run (profile fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init profile fn2-core))
      ((mv g fn2-core) (fn2-principals-genesis profile fn2-core))
      ((mv a fn2-core) (fn2-as-lookup "anonymous" fn2-core))
      ((mv o fn2-core) (fn2-as-lookup "owner" fn2-core))
      ((mv m fn2-core) (fn2-as-lookup "mini" fn2-core))
      ((mv o1 fn2-core) (fn2-as-lookup "owners" fn2-core))
      ((mv o2 fn2-core) (fn2-as-lookup "owne" fn2-core))
      ((mv sc sid fn2-core) (mv-let (c i) (fn2-principal-of-slot 2 fn2-core) (mv c i fn2-core))))
  (mv (list g a o m o1 o2 (list sc sid)) fn2-core)))
(defun fn2-as-genesis (profile)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-as-genesis-run profile fn2-core) r)))

(defconst *fn2-as-anonymous-id* 1)                        ; slot 0, incarnation 1
(defconst *fn2-as-owner-id* (+ (* 2 4294967296) 1))       ; slot 2, incarnation 1
(defun fn2-authority-genesis-positive ()
 (declare (xargs :verify-guards nil))
 (let ((boot1 (fn2-as-genesis *fn2-as-profile*))
       (boot2 (fn2-as-genesis *fn2-as-profile*)))
  (and (equal boot1
              (list :ok (list :ok *fn2-as-anonymous-id*) (list :ok *fn2-as-owner-id*)
                    '(:absent 0) '(:absent 0) '(:absent 0) (list :ok *fn2-as-owner-id*)))
       (not (equal *fn2-as-anonymous-id* *fn2-as-owner-id*))
       (equal boot2 boot1))))
(assert-event (fn2-authority-genesis-positive))
;; No owner slot below the system row (P = 1): anonymous only.
(assert-event
 (let ((r (fn2-as-genesis (put-assoc-equal :p 1 *fn2-as-profile*))))
  (and (equal (nth 0 r) :ok) (equal (nth 1 r) (list :ok *fn2-as-anonymous-id*)) (equal (car (nth 2 r)) :absent))))

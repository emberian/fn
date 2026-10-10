;;; S038: the reclaim slot's capture and release, over the DEPLOYED host
;;; entries (host/owner-host.lisp fn-owner-orc-capture, fn-owner-orc-finish,
;;; fn-owner-sco-publication-done) and the deployed ACL2 decisions they ask
;;; (books/owner-reclaim.lisp fn-orc-capture-slot, fn-orc-capture-word,
;;; fn-orc-release-slot), against the owner's globals as a table.  The Store
;;; and configuration accessors are data readers: no decision of the slot's
;;; is made by them.  Each case asserts what the caller is answered AND the
;;; slot (the record's :pass and :inflight) after it.
(require :sb-posix)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(declaim (declaration xargs))

(defun load-deployed-forms (path wanted)
  "Evaluate PATH's top-level forms named by WANTED, (KIND NAME) each; a defun
loses its xargs declaration."
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            when (and (consp form)
                      (member (list (car form) (cadr form)) wanted :test #'equal))
              do (eval (destructuring-bind (name formals &rest body) (cdr form)
                         `(defun ,name ,formals
                            ,@(remove-if (lambda (f) (and (consp f) (eq (car f) 'declare)
                                                          (consp (cadr f))
                                                          (eq (car (cadr f)) 'xargs)))
                                         body))))
                 (setf missing (remove (list (car form) (cadr form)) missing :test #'equal))))
    (when missing (error "deployed forms missing from ~a: ~s" path missing))))

(defun natp (x) (and (integerp x) (<= 0 x)))
(defun posp (x) (and (integerp x) (< 0 x)))
(defun zp (x) (not (posp x)))
(defun len (x) (length x))
(defun true-listp (x) (null (cdr (last x))))
(defun member-eq (x l) (member x l :test #'eq))
(defmacro value (x) `(values nil ,x state))
(defmacro mbe (&key logic exec) (declare (ignore logic)) exec)
(defmacro mv (&rest xs) `(values ,@xs))
(defmacro mv-let (vars form &body body) `(multiple-value-bind ,vars ,form ,@body))
(defun update-nth (n v l)
  (if (zerop n) (cons v (cdr l)) (cons (car l) (update-nth (1- n) v (cdr l)))))

(load-deployed-forms "books/owner-reclaim.lisp"
 '((defun fn-orc-capture-word) (defun fn-orc-capture-slot) (defun fn-orc-release-slot)))
(defvar *state* (make-hash-table))
(defun boundp-global (key state) (nth-value 1 (gethash key state)))
(defun f-get-global (key state) (gethash key state))
(defun f-put-global (key val state) (setf (gethash key state) val) state)
;; The slot's fields are one carried record in the owner's global
;; fn-owner-publication (books/owner-publication-state.lisp).
(load-deployed-forms "books/owner-publication-state.lisp"
 '((defun fn-opub-initial) (defun fn-opub-index) (defun fn-opub-get) (defun fn-opub-put)
   (defun fn-ost-publication) (defun fn-ost-install-publication)))
(load-deployed-forms "books/owner-publication-transitions.lisp"
 '((defun fn-opub-done)))
(load-deployed-forms "books/consumer-position-fields.lisp" '((defun fn-cp-nth)))
(load-deployed-forms "books/store-checkpoint-accessors.lisp" '((defun fn-sco-at)))
(load-deployed-forms "books/store-checkpoint-open.lisp"
 '((defun fn-sco-records) (defun fn-sco-sequence)))
(load-deployed-forms "host/owner-host.lisp"
 '((defun fn-owner-orc-pass) (defun fn-owner-orc-capture) (defun fn-owner-orc-finish)
   (defun fn-owner-sco-publication-done)))

;; Data readers and a recording seam (nothing here decides the slot).
(defvar *rows* '(r0 r1 r2 r3 r4))
(defun fn-owner-core (state) (declare (ignore state)) :owner)
(defun fn-own-store (owner) (declare (ignore owner)) :store)
(defun fn-sn-files (st) (declare (ignore st)) :files)
(defun fn-sf-records (files) (declare (ignore files)) *rows*)
(defun fn-sf-records-count (files) (declare (ignore files)) (length *rows*))
(defun fn-sn-config-history (st) (declare (ignore st)) :history)
(defun fn-sf-frontier (files) (declare (ignore files)) :frontier)
(defun fn-owner-store-profile (state) (declare (ignore state)) nil)
(defun fn-owner-ocfg (state) (declare (ignore state)) :ocfg)
(defun fn-ocfg-config (oc) (declare (ignore oc)) :config)
(defun fn-cfg-value (c) (declare (ignore c)) :v)
(defun fn-record-stamp-of-observation (clock) (declare (ignore clock)) 7)
(defun fn-rcl-owner-feed-holders (owner) (declare (ignore owner)) :feeds)
(defun fn-scka-strip-base (next) next)
(defun fn-owner-sco-budget (override profile) (declare (ignore override profile)) nil)
(defun fn-bs-profile-max-record-octets (profile) (declare (ignore profile)) nil)

(defun check (ok label)
  (unless ok (format t "RECLAIM_SLOT_ASSERTION:~a~%" label) (error "~a" label)))
(defun slot () (let ((r (fn-ost-publication *state*)))
                 (list (fn-opub-get :pass r) (fn-opub-get :inflight r))))
(defun set-slot (pass inflight)
  (fn-ost-install-publication
   (fn-opub-put :inflight inflight (fn-opub-put :pass pass (fn-ost-publication *state*)))
   *state*))
(defun capture (mode)
  (multiple-value-bind (erp answer st) (fn-owner-orc-capture mode :clock nil nil :rev *state*)
    (declare (ignore st))
    (check (null erp) "capture is not an error")
    answer))
(defun finish () (fn-owner-orc-finish *state*))
;; NEXT's records are the captured prefix: a checkpoint whose second slot
;; holds COUNT rows.
(defun next-of (count) (list :checkpoint (make-list count :initial-element :row)))
(defun publication-done (count)
  (fn-owner-sco-publication-done (next-of count) 0 nil nil *state*))

;; A free slot: a recorded capture takes it at COUNT, and is the whole answer.
(set-slot nil nil)
(let ((answer (capture :recorded)))
  (check (and (consp answer) (= (length answer) 13)) "a free slot answers the capture")
  (check (equal (slot) '(:recorded 5)) "a writing capture holds the pass and COUNT"))

;; A pass in flight refuses every other capture by name and writes nothing.
(check (equal (capture :recorded) '(:refused :in-flight)) "second recorded capture refused")
(check (equal (slot) '(:recorded 5)) "refusal leaves the slot")
(check (equal (capture :dry-run) '(:refused :in-flight)) "dry run refused beside a writing pass")
(check (equal (slot) '(:recorded 5)) "dry-run refusal leaves the slot")

;; A publication's done step for another count leaves the writing pass's hold.
(publication-done 3)
(check (equal (slot) '(:recorded 5)) "a publication's done never frees a pass's hold")
(publication-done 5)
(check (equal (slot) '(:recorded 5)) "nor at the same count while a writing pass holds the slot")

;; The pass's own finish frees both.
(finish)
(check (equal (slot) '(nil nil)) "the holder's finish frees pass and inflight")
(finish)
(check (equal (slot) '(nil nil)) "a finish with nothing in flight changes nothing")

;; A publication in flight: a writing capture is queued behind it, by name;
;; a dry run takes the pass and leaves INFLIGHT alone.
(set-slot nil 4)
(check (equal (capture :recorded) '(:refused :queued)) "a writing capture queues behind a publication")
(check (equal (slot) '(nil 4)) "queued refusal leaves the slot")
(let ((answer (capture :dry-run)))
  (check (and (consp answer) (= (length answer) 13)) "a dry run is captured beside a publication"))
(check (equal (slot) '(:dry-run 4)) "a dry run holds the pass, not INFLIGHT")
(finish)
(check (equal (slot) '(nil 4)) "a dry run's finish leaves the publication's hold")
(publication-done 3)
(check (equal (slot) '(nil 4)) "a publication releases only its own count")
(publication-done 4)
(check (equal (slot) '(nil nil)) "the publication's done at its count frees INFLIGHT")

;; A publication's done while a dry run holds the pass: the publication frees
;; its own hold, the dry run's stays.
(set-slot :dry-run 4)
(publication-done 4)
(check (equal (slot) '(:dry-run nil)) "a dry run does not keep a publication's hold")
(finish)
(check (equal (slot) '(nil nil)) "then the dry run's finish frees the pass")

(format t "RECLAIM_SLOT_PASS the capture refuses a held slot by name and writes nothing; each release frees only its holder's hold~%")

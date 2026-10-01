; Historical control configuration from SAME accepted joint C decisions.
; This low cursor retrieves a captured value; it grants no source custody,
; current account authority or allocation allowance. Actual caller owns those.
(in-package "ACL2")
(include-book "config")
(include-book "consumer-position-fields")

(defun fn-ccpx-entry (config sequence txid keyring source predecessor)
 (declare (xargs :guard t))
 (list :control-config-projection config (fn-cfg-generation config)
       sequence txid keyring source predecessor))

; Fixed-width header only: never traverse CONFIG or the predecessor chain.
(defun fn-ccpx-headerp (x)
 (declare (xargs :guard t))
 (and (fn-cbor-at-mostp x 8) (true-listp x) (equal (len x) 8)
      (eq (fn-cp-nth 0 x) :control-config-projection)
      (natp (fn-cp-nth 2 x)) (natp (fn-cp-nth 3 x))
      (natp (fn-cp-nth 4 x)) (natp (fn-cp-nth 5 x))))

(defun fn-ccpx-answer (entry)
 (declare (xargs :guard t))
 (list :configuration (fn-cp-nth 1 entry) (fn-cp-nth 2 entry)
       (fn-cp-nth 3 entry) (fn-cp-nth 4 entry) (fn-cp-nth 5 entry)
       (fn-cp-nth 6 entry)))

; Logical reference only. Newest-first is established by actual publisher:
; monotone Ctxid/Csequence, newest same-txid last publication first in spine.
(local (defthm fn-ccpx-header-is-consp
 (implies (fn-ccpx-headerp x) (consp x))
 :hints (("Goal" :in-theory (enable fn-ccpx-headerp fn-cp-nth)))))

(defun fn-ccpx-at (chain query)
 (declare (xargs :guard t :verify-guards nil :measure (acl2-count chain)
                  :hints (("Goal" :in-theory (disable fn-ccpx-headerp fn-cp-nth)))))
 (cond ((not (fn-ccpx-headerp chain)) '(:unavailable :historical-config-prefix))
       ((not (natp query)) '(:refused :historical-config-coordinate))
       ((<= (fn-cp-nth 4 chain) query) (fn-ccpx-answer chain))
       (t (fn-ccpx-at (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr chain)))))))) query))))

(defun fn-ccpx-begin (chain query captured-source)
 (declare (xargs :guard t))
 (if (natp query)
     (list :yield (list :control-config-lookup query chain chain captured-source))
   '(:refused :historical-config-coordinate)))

; One projection entry per scheduling tick. The borrowed captured root/source
; stay literal. Recorded entry source is provenance, not today's live token.
(defun fn-ccpx-tick (cursor)
 (declare (xargs :guard t))
 (let ((query (fn-cp-nth 1 cursor)) (entry (fn-cp-nth 3 cursor)))
  (cond ((not (and (fn-cbor-at-mostp cursor 5) (true-listp cursor)
                   (equal (len cursor) 5)
                   (eq (fn-cp-nth 0 cursor) :control-config-lookup) (natp query)))
         '(:refused :historical-config-cursor))
        ((not (fn-ccpx-headerp entry)) '(:unavailable :historical-config-prefix))
        ((<= (fn-cp-nth 4 entry) query) (fn-ccpx-answer entry))
        (t (list :yield (list :control-config-lookup query (fn-cp-nth 2 cursor)
                             (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr entry)))))))) (fn-cp-nth 4 cursor)))))))

(defthm fn-ccpx-yield-preserves-complete-lookup
 (implies (equal (fn-cp-nth 0 (fn-ccpx-tick cursor)) :yield)
  (equal (fn-ccpx-at (fn-cp-nth 3 (fn-cp-nth 1 (fn-ccpx-tick cursor)))
                    (fn-cp-nth 1 (fn-cp-nth 1 (fn-ccpx-tick cursor))))
         (fn-ccpx-at (fn-cp-nth 3 cursor) (fn-cp-nth 1 cursor))))
 :hints (("Goal"
          :expand ((fn-ccpx-at (fn-cp-nth 3 cursor) (fn-cp-nth 1 cursor)))
          :in-theory (e/d (fn-ccpx-tick fn-cp-nth fn-ccpx-answer)
                          (fn-ccpx-at fn-ccpx-headerp)))))

(defthm fn-ccpx-selected-complete-result
 (implies (equal (fn-cp-nth 0 (fn-ccpx-tick cursor)) :configuration)
  (equal (fn-ccpx-tick cursor)
         (fn-ccpx-at (fn-cp-nth 3 cursor) (fn-cp-nth 1 cursor))))
 :hints (("Goal"
          :expand ((fn-ccpx-at (fn-cp-nth 3 cursor) (fn-cp-nth 1 cursor)))
          :in-theory (e/d (fn-ccpx-tick fn-cp-nth fn-ccpx-answer)
                          (fn-ccpx-at fn-ccpx-headerp)))))

(in-theory (disable fn-ccpx-entry fn-ccpx-headerp fn-ccpx-answer fn-ccpx-at
                    fn-ccpx-begin fn-ccpx-tick))

; Actual static/redeemed credential selection with paired signing intent.
; The candidate and intent trie share the same successful first-insertion
; decision. A static binding search and a candidate list traversal each
; inspect one cell per tick. These pending inputs never authorize requests.
(in-package "ACL2")
(include-book "consumer-account-candidate")

; Fixed10: candidate, intent trie+metadata, immutable parsed binding source,
; borrowed binding cursor, origin/mode/principal and scheduler phase.
(defun fn-aic-state (candidate intents im bindings cursor origin mode principal phase)
 (declare (xargs :guard t))
 (list :account-input candidate intents im bindings cursor origin mode principal phase))

(defun fn-aic-initial (policy bindings)
 (declare (xargs :guard t))
 (fn-aic-state (fn-cad-initial policy) nil nil bindings nil nil nil nil :idle))

(defun fn-aic-intent (origin mode principal)
 (declare (xargs :guard t))
 (list :account-intent origin mode principal))

(defun fn-aic-intent-carry (origin mode)
 (declare (xargs :guard t))
 (fn-caac-spine (list (fn-caac-atom :account-intent) (fn-caac-atom origin)
                       (fn-caac-atom mode) (fn-scs-octets 32))))

; Origin0 is parsed static source, origin1 an eligible current redeemed row.
; Both are selected by the core driver, never by the native transport.
(defun fn-aic-feed (s credential origin)
 (declare (xargs :guard t))
 (if (or (not (eq (fn-cp-nth 9 s) :idle))
         (not (member-equal origin '(0 1))))
     '(:refused :account-input-phase)
  (let ((one (fn-cad-feed (fn-cp-nth 1 s) credential)))
   (if (not (eq (fn-cp-nth 0 one) :yield)) one
    (list :yield
     (fn-aic-state (fn-cp-nth 1 one) (fn-cp-nth 2 s) (fn-cp-nth 3 s)
                   (fn-cp-nth 4 s) (if (equal origin 0) (fn-cp-nth 4 s) nil)
                   origin (if (equal origin 0) 1 0) (make-list 32 :initial-element 0)
                   (if (equal origin 0) :binding :candidate)))))))

(defun fn-aic-tick (s)
 (declare (xargs :guard t))
 (let* ((candidate (fn-cp-nth 1 s)) (intents (fn-cp-nth 2 s)) (im (fn-cp-nth 3 s))
        (bindings (fn-cp-nth 4 s)) (cursor (fn-cp-nth 5 s))
        (origin (fn-cp-nth 6 s)) (mode (fn-cp-nth 7 s)) (principal (fn-cp-nth 8 s)))
  (case (fn-cp-nth 9 s)
   (:idle (list :ready s))
   (:binding
    (if (consp cursor)
        (if (equal (fn-auth-cred-name (fn-cp-nth 4 candidate)) (fn-ag-car (car cursor)))
            (let ((value (fn-ag-cdr (car cursor))))
             (if (and (fn-cbor-at-mostp value 32) (fn-cbor-octet-listp value)
                      (equal (len value) 32))
                 (list :yield (fn-aic-state candidate intents im bindings nil origin 2 value :candidate))
               '(:refused :account-input-binding)))
          (list :yield (fn-aic-state candidate intents im bindings (cdr cursor)
                                    origin mode principal :binding)))
      (list :yield (fn-aic-state candidate intents im bindings nil origin 1 principal :candidate))))
   (:candidate
    (let* ((credential (fn-cp-nth 4 candidate)) (name (fn-auth-cred-name credential))
           (suffix (fn-cp-nth 6 candidate)) (head (if (consp suffix) (car suffix) nil))
           (insertp (and (eq (fn-cp-nth 1 candidate) :seek)
                         (or (not head) (fn-caa-name-lessp name (fn-auth-cred-name head)))))
           (one (fn-cad-tick candidate)) (word (fn-cp-nth 0 one)))
     (if (not (member-eq word '(:ready :yield))) one
      (mv-let (next-index next-im)
       (if insertp
           (fn-cait-put-octets name (fn-aic-intent origin mode principal)
                               (fn-aic-intent-carry origin mode) intents im)
         (mv intents im))
       (list word
        (fn-aic-state (fn-cp-nth 1 one) next-index next-im bindings nil
                      origin mode principal (if (eq word :ready) :idle :candidate)))))))
   (otherwise '(:refused :account-input-phase)))))

(in-theory (disable fn-aic-state fn-aic-initial fn-aic-intent fn-aic-intent-carry
                    fn-aic-feed fn-aic-tick))

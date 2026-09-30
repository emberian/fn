; Account-adoption input preparation used by the actual owner scheduler.
; Feed credentials in the existing static-first/source-row order. Duplicate
; logins retain the first credential, exactly as fn-auth-find-cred does.
; Each tick inspects or rebuilds one ordered-list cell; no sort/reverse or
; whole credential-table recognizer runs at the publication fence.
; Source/retained-graph funding and owner capture are separate obligations.
(in-package "ACL2")
(include-book "consumer-account-carried")

; Fixed11: tag phase installed-list/listmeta credential/credentialcarry,
; borrowed suffix/suffixmeta, reversed prefix/prefixmeta, policy.
(defun fn-cad-state (phase rows metadata credential carry suffix sm reversed rm policy)
 (declare (xargs :guard t))
 (list :account-candidate phase rows metadata credential carry suffix sm reversed rm policy))

(defun fn-cad-initial (policy)
 (declare (xargs :guard t))
 (fn-cad-state :idle nil nil nil nil nil nil nil nil policy))

; Bounds are the existing credential grammar, checked before its recognizer.
; This protects total malformed-input calls too; it does not cap table size.
(defun fn-cad-bounded-credp (credential)
 (declare (xargs :guard t))
 (let ((secret (fn-auth-cred-secret credential)))
  (and (fn-cbor-at-mostp credential 5)
       (fn-cbor-at-mostp (fn-auth-cred-name credential) *fn-auth-max-name-octets*)
       (fn-cbor-at-mostp (fn-auth-cred-principal credential) 32)
       (fn-cbor-at-mostp secret 5)
       (fn-cbor-at-mostp (fn-cp-nth 1 secret) 16)
       (fn-cbor-at-mostp (fn-cp-nth 2 secret) 32)
       (fn-cbor-at-mostp (fn-cp-nth 3 secret) 32)
       (fn-cbor-at-mostp (fn-cp-nth 4 secret) 32)
       (fn-auth-credp credential))))

(defun fn-cad-feed (s credential)
 (declare (xargs :guard t))
 (if (or (not (eq (fn-cp-nth 1 s) :idle))
         (not (fn-cad-bounded-credp credential)))
     '(:refused :candidate-credential)
  (list :yield
   (fn-cad-state :seek (fn-cp-nth 2 s) (fn-cp-nth 3 s)
                 credential (fn-caac-credential-value-carry credential)
                 (fn-cp-nth 2 s) (fn-cp-nth 3 s) nil nil (fn-cp-nth 10 s)))))

(defun fn-cad-tick (s)
 (declare (xargs :guard t))
 (let* ((phase (fn-cp-nth 1 s))
        (rows (fn-cp-nth 2 s)) (metadata (fn-cp-nth 3 s))
        (credential (fn-cp-nth 4 s)) (carry (fn-cp-nth 5 s))
        (suffix (fn-cp-nth 6 s)) (sm (fn-cp-nth 7 s))
        (reversed (fn-cp-nth 8 s)) (rm (fn-cp-nth 9 s))
        (policy (fn-cp-nth 10 s)))
  (case phase
   (:idle (list :ready s))
   (:seek
    (let* ((head (if (consp suffix) (car suffix) nil))
           (name (fn-auth-cred-name credential))
           (old-name (fn-auth-cred-name head)))
     (cond
      ((and head (equal name old-name))
       ; Preserve the first source credential, including principal/verifier.
       (list :ready (fn-cad-state :idle rows metadata nil nil nil nil nil nil policy)))
      ((or (not head) (fn-caa-name-lessp name old-name))
       (list :yield
        (fn-cad-state :rebuild rows metadata nil nil
                      (cons credential suffix) (fn-caac-list-cons carry sm)
                      reversed rm policy)))
      (t
       (list :yield
        (fn-cad-state :seek rows metadata credential carry
                      (if (consp suffix) (cdr suffix) nil) (fn-cp-nth 2 sm)
                      (cons head reversed)
                      (fn-caac-list-cons (fn-cp-nth 1 sm) rm) policy))))))
   (:rebuild
    (if (consp reversed)
        (list :yield
         (fn-cad-state :rebuild rows metadata nil nil
                       (cons (car reversed) suffix)
                       (fn-caac-list-cons (fn-cp-nth 1 rm) sm)
                       (cdr reversed) (fn-cp-nth 2 rm) policy))
      (list :ready (fn-cad-state :idle suffix sm nil nil nil nil nil nil policy))))
   (otherwise '(:refused :candidate-phase)))))

; One actual operation selected from the already prepared candidate and the
; current carried old-account cursor. The row token uses the ACTUAL projected
; transaction coordinate; the owner must persist that same coordinate, not a
; provisional allocation promise. Candidate advancement occurs only durable.
(defun fn-cad-row-operation (candidate base credential coordinate)
 (declare (xargs :guard t))
 (let ((secret (fn-auth-cred-secret credential)))
  (list :authority-row candidate base (fn-auth-cred-name credential) coordinate
        (fn-auth-cred-principal credential) (fn-cp-nth 1 secret)
        (fn-cp-nth 2 secret) (fn-cp-nth 3 secret) (fn-cp-nth 4 secret)
        (if (fn-auth-cred-postingp credential) 1 0))))

(defun fn-cad-authority-operation (cp candidate credentials policy projected-txid)
 (declare (xargs :guard t))
 (let* ((a (fn-cp-nth 6 cp)) (p (fn-cp-nth 5 a))
        (prep (fn-cp-nth 5 p)) (old (fn-cp-nth 2 prep))
        (head (if (consp old) (car old) nil))
        (credential (if (consp credentials) (car credentials) nil))
        (name (fn-auth-cred-name credential)) (base (fn-cp-nth 1 a)))
  (cond
   ((not p)
    (list :operation (list :authority-begin candidate base (fn-cp-nth 2 a) policy) nil))
   ((not (equal candidate (fn-cp-nth 1 p))) '(:refused :candidate-not-current))
   ((eq (fn-cp-nth 1 prep) :merge)
    (cond
     ((and head (or (not credential) (fn-caa-name-lessp (fn-cp-nth 1 head) name)))
      (list :operation
       (list :authority-tombstone candidate base (fn-cp-nth 1 head)
             (fn-cp-creation-coordinate (fn-cp-nth 2 head))) nil))
     (credential
      (list :operation
       (fn-cad-row-operation candidate base credential
        (if (and head (equal name (fn-cp-nth 1 head)) (fn-cp-nth 3 head))
            (fn-cp-creation-coordinate (fn-cp-nth 2 head)) projected-txid)) t))
     (t (list :operation
          (list :authority-seal candidate base (fn-cp-nth 3 p) (fn-cp-nth 7 p)) nil))))
   ((eq (fn-cp-nth 1 prep) :reverse)
    (list :operation (list :authority-prepare candidate base) nil))
   ((eq (fn-cp-nth 1 prep) :ready)
    (list :operation
     (list :authority-fence candidate base (fn-cp-nth 3 p) (fn-cp-nth 7 p)) nil))
   (t '(:refused :candidate-preparation-phase)))))

(defun fn-cad-authority-event (sequence txid generation selection)
 (declare (xargs :guard t))
 (if (eq (fn-cp-nth 0 selection) :operation)
     (let ((event (list :consumer-authority sequence txid generation
                        (fn-cp-nth 1 selection))))
      (if (fn-cac-eventp event) (list :ok event (fn-cp-nth 2 selection))
       '(:refused :account-event-representation)))
  selection))

; Native dispatch reads only ACL2's bounded action fields. It does not choose
; which credential, source row, operation, projected coordinate or policy wins.
(defun fn-cad-action-kind (action)
 (declare (xargs :guard t))
 (fn-cp-nth 0 action))

(defun fn-cad-action-value (action)
 (declare (xargs :guard t))
 (fn-cp-nth 1 action))

(in-theory (disable fn-cad-state fn-cad-initial fn-cad-bounded-credp fn-cad-feed
                    fn-cad-tick fn-cad-row-operation fn-cad-authority-operation
                    fn-cad-authority-event fn-cad-action-kind fn-cad-action-value))

; PRF-1142 / SCN-1048. INITIAL's structured request evaluator.
; Only the installed operation-source readout can authorize these records.
; Recognizing their representation grants neither an image nor a turn.
(in-package "ACL2")
(include-book "page-maintenance-lease")

(defun fn-sni-widthp (x n)
  (declare (xargs :guard (natp n)))
  (if (zp n) (null x)
    (and (consp x) (fn-sni-widthp (cdr x) (1- n)))))

; The immutable role table is returned by the SAME installed association.
; Each entry is (role memory-class actual-body-coordinate).  INITIAL's
; disk/descriptors/worker/identity come from its operation, not heap rows.
(defun fn-sni-role-entry (role table)
  (declare (xargs :guard t))
  (if (consp table)
      (if (equal role (fn-prl-nth 0 (car table))) (car table)
        (fn-sni-role-entry role (cdr table))) nil))

(defun fn-sni-request-octets (requests table)
  (declare (xargs :guard t))
  (if (consp requests)
      (let* ((r (car requests))
             (entry (fn-sni-role-entry (fn-prl-nth 1 r) table)))
        (if (not (and (fn-sni-widthp r 5)
                      (equal (fn-prl-nth 0 r) :request)
                      (fn-sni-widthp entry 3)
                      (member-eq (fn-prl-nth 1 entry)
                                 '(:heap :stack :tls :external))
                      (equal (fn-prl-nth 2 r) (fn-prl-nth 2 entry))
                      (natp (fn-prl-nth 3 r))
                      (natp (fn-prl-nth 4 r))))
            (mv :unavailable nil)
          (mv-let (word rest) (fn-sni-request-octets (cdr requests) table)
            (if (equal word :available)
                (mv :available (+ (* (fn-prl-nth 3 r) (fn-prl-nth 4 r))
                                  (nfix rest)))
              (mv :unavailable nil)))))
    (if (null requests) (mv :available 0) (mv :unavailable nil))))

; Six ordered source streams remain separate, preserving their provenance.
(defun fn-sni-family-octets (family table)
  (declare (xargs :guard t))
  (if (not (and (fn-sni-widthp family 15)
                (equal (fn-prl-nth 0 family) :runtime-operation-family)
                (equal (fn-prl-nth 1 family) :initial)))
      (mv :unavailable nil)
    (mv-let (pword primary) (fn-sni-request-octets (fn-prl-nth 7 family) table)
     (mv-let (cword caller) (fn-sni-request-octets (fn-prl-nth 8 family) table)
      (mv-let (fword firstuse) (fn-sni-request-octets (fn-prl-nth 9 family) table)
       (mv-let (gword collector) (fn-sni-request-octets (fn-prl-nth 10 family) table)
        (mv-let (eword external) (fn-sni-request-octets (fn-prl-nth 11 family) table)
         (mv-let (kword control) (fn-sni-request-octets (fn-prl-nth 12 family) table)
          (if (and (equal pword :available) (equal cword :available)
                   (equal fword :available) (equal gword :available)
                   (equal eword :available) (equal kword :available))
              (mv :available (+ (nfix primary) (nfix caller) (nfix firstuse)
                                (nfix collector) (nfix external) (nfix control)))
            (mv :unavailable nil))))))))))

(defun fn-sni-initial-demand (family table)
  (declare (xargs :guard t))
  (mv-let (word resident) (fn-sni-family-octets family table)
    (if (equal word :available)
        ; The first image header is reserved now; target and both digest
        ; spools grow after exact census. Three private FDs are reserved
        ; before opening. The actual source PRF pin has its own same-pool
        ; child descriptor/identity charge; these three are private backing
        ; roles only and do not substitute for that pin's admission.
        (mv :available (list (nfix resident) 16384 3 1 1))
      (mv :unavailable nil))))

(defthm fn-sni-request-octets-natural
  (implies (equal (mv-nth 0 (fn-sni-request-octets requests table)) :available)
           (natp (mv-nth 1 (fn-sni-request-octets requests table))))
  :hints (("Goal" :induct (fn-sni-request-octets requests table)
           :in-theory (enable fn-sni-request-octets))))

(defthm fn-sni-demand-has-operation-resource-roles
  (implies (equal (mv-nth 0 (fn-sni-initial-demand family table)) :available)
           (let ((d (mv-nth 1 (fn-sni-initial-demand family table))))
             (and (fn-prs-vectorp d)
                  (equal (fn-prl-nth 1 d) 16384)
                  (equal (fn-prl-nth 2 d) 3)
                  (equal (fn-prl-nth 3 d) 1)
                  (equal (fn-prl-nth 4 d) 1))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-sni-initial-demand fn-prs-vectorp
                 fn-prs-nats-p fn-prl-nth)
                (fn-sni-family-octets fn-sni-request-octets)))))

(in-theory (disable fn-sni-widthp fn-sni-role-entry fn-sni-request-octets
                    fn-sni-family-octets fn-sni-initial-demand))

; The BP receipt's byte comparison by handle (lane bp-catalog, wave 5).
;
; The receiver's acceptance of a request (books/bp-native-app-fast.lisp
; fn-bpaj-request-acceptable-fast, and its projected and transit twins)
; compares the request's article octets with the committed record's payload:
; (equal (fn-bpa-request-article request) (fn-record-payload record)).  Over
; the held record of the catalog (books/catalog-record.lisp) the payload is a
; handle into the arena, and materializing it (fn-held-wire-of, which conses
; the slice through fn-arena-payload) to compare is the octet-list copy the
; BP path must not make.  fn-bphh-octets-at-p compares in place, one
; fn-arena-get per octet, and conses nothing.
;
; Boundary theorem: fn-bphh-request-article-matches-is-wire, the in-place
; comparison IS the list model's conjunct over the materialized record.
; Host: NONE YET.  The owner's Store holds no catalog on dev (catalog-slice
; steps 7 and 8), so the receipt still reads the list record; this is the
; comparison the receipt takes when the Store hands it a row and a handle.
(in-package "ACL2")
(include-book "catalog-record")
(include-book "bp-adu")
(set-verify-guards-eagerness 2)

(defun fn-bphh-octets-at-p (octets h i fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (natp i)
                              (< h (fn-arena-count fn-arena)))
                  :measure (len octets)))
  (if (atom octets)
      (and (null octets) (equal (nfix i) (fn-arena-payload-len h fn-arena)))
    (and (< (nfix i) (fn-arena-payload-len h fn-arena))
         (equal (car octets) (fn-arena-get h (nfix i) fn-arena))
         (fn-bphh-octets-at-p (cdr octets) h (1+ (nfix i)) fn-arena))))

(local
 (defthmd fn-bphh-nthcdr-opens
   (implies (and (natp i) (< i (len p)))
            (equal (nthcdr i p) (cons (nth i p) (nthcdr (1+ i) p))))))

(local
 (defthm fn-bphh-nthcdr-past-end
   (implies (and (true-listp p) (natp i) (<= (len p) i))
            (equal (nthcdr i p) nil))))

(local
 (defthm fn-bphh-nthcdr-inside-nonnil
   (implies (and (natp i) (< i (len p)))
            (iff (nthcdr i p) t))
   :hints (("Goal" :use fn-bphh-nthcdr-opens))))

(local
 (defthm fn-bphh-equal-nthcdr-when-inside
   (implies (and (natp i) (< i (len p)))
            (equal (equal x (nthcdr i p))
                   (and (consp x)
                        (equal (car x) (nth i p))
                        (equal (cdr x) (nthcdr (1+ i) p)))))
   :hints (("Goal" :use fn-bphh-nthcdr-opens))))

(local
 (defthm fn-bphh-octets-at-p-is-nthcdr
   (implies (and (natp i) (true-listp (fn-arena-payload h fn-arena))
                 (<= i (len (fn-arena-payload h fn-arena))))
            (equal (fn-bphh-octets-at-p octets h i fn-arena)
                   (equal octets (nthcdr i (fn-arena-payload h fn-arena)))))
   :hints (("Goal" :induct (fn-bphh-octets-at-p octets h i fn-arena)
            :in-theory (e/d (fn-arena-payload-is-nth fn-arena-get-is-nth
                             fn-arena-payload-len-is-len-nth)
                            (nthcdr))))))

(local
 (defthm fn-bphh-payload-listp-nth-true-listp
   (implies (fn-arn-payload-listp xs)
            (true-listp (nth h xs)))
   :hints (("Goal" :in-theory (enable nth fn-cbor-octet-listp)))))

(defthm fn-bphh-octets-at-p-is-equal-payload
  (implies (fn-arena-p fn-arena)
           (equal (fn-bphh-octets-at-p octets h 0 fn-arena)
                  (equal octets (fn-arena-payload h fn-arena))))
  :hints (("Goal" :use ((:instance fn-bphh-octets-at-p-is-nthcdr (i 0)))
           :in-theory (e/d (fn-arena-payload-is-nth fn-arena-p-is-payload-listp)
                           (fn-bphh-octets-at-p)))))

(defun fn-bphh-request-article-matches (request held fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp (fn-record-payload held))
                              (< (fn-record-payload held)
                                 (fn-arena-count fn-arena)))))
  (fn-bphh-octets-at-p (fn-bpa-request-article request)
                       (fn-record-payload held) 0 fn-arena))

; Keystone: the in-place comparison is the acceptance conjunct over the
; materialized wire record.
(defthm fn-bphh-request-article-matches-is-wire
  (implies (fn-arena-p fn-arena)
           (equal (fn-bphh-request-article-matches request held fn-arena)
                  (equal (fn-bpa-request-article request)
                         (fn-record-payload (fn-held-wire-of held fn-arena)))))
  :hints (("Goal" :in-theory (enable fn-held-wire-of fn-held-wire))))

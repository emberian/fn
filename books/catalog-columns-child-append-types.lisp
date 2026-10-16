; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-constructor-storage-types")

(defthm fn-lbc-msgid-octetsp-of-append
 (implies (and (fn-lbc-msgid-octetsp rows) (adt-rec-p (QUOTE ((:U8))) rec))
 (fn-lbc-msgid-octetsp (fn-lbc-msgid-octets-append rec rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-msgid-octets-append{preserved} (fn-lbc-msgid-octets rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-octetsp fn-lbc-msgid-octets-append)))))

(defthm fn-lbc-overview-octetsp-of-append
 (implies (and (fn-lbc-overview-octetsp rows) (adt-rec-p (QUOTE ((:U8))) rec))
 (fn-lbc-overview-octetsp (fn-lbc-overview-octets-append rec rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-overview-octets-append{preserved} (fn-lbc-overview-octets rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-overview-octetsp fn-lbc-overview-octets-append)))))

(defthm fn-lbc-rowwordsp-of-append
 (implies (and (fn-lbc-rowwordsp rows) (adt-rec-p (QUOTE ((:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64))) rec))
 (fn-lbc-rowwordsp (fn-lbc-rowwords-append rec rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-rowwords-append{preserved} (fn-lbc-rowwords rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-rowwordsp fn-lbc-rowwords-append)))))

(defthm fn-lbc-directoryp-of-append
 (implies (and (fn-lbc-directoryp rows) (adt-rec-p (QUOTE ((:U64) (:U64) (:U64) (:BOOL) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:BOOL) (:BOOL) (:BOOL) (:U64) (:BOOL))) rec))
 (fn-lbc-directoryp (fn-lbc-directory-append rec rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-directory-append{preserved} (fn-lbc-directory rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-directoryp fn-lbc-directory-append)))))

(defthm fn-lbc-membershipsp-of-append
 (implies (and (fn-lbc-membershipsp rows) (adt-rec-p (QUOTE ((:U64) (:U64) (:U64))) rec))
 (fn-lbc-membershipsp (fn-lbc-memberships-append rec rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-memberships-append{preserved} (fn-lbc-memberships rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-membershipsp fn-lbc-memberships-append)))))

(defthm fn-lbc-novp-of-append
 (implies (and (fn-lbc-novp rows) (adt-rec-p (QUOTE ((:BOOL) (:BOOL) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64) (:U64))) rec))
 (fn-lbc-novp (fn-lbc-nov-append rec rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-nov-append{preserved} (fn-lbc-nov rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-novp fn-lbc-nov-append)))))

(defthm fn-lbc-msgid-slotsp-of-append
 (implies (and (fn-lbc-msgid-slotsp rows) (adt-rec-p '((:u64)) rec))
 (fn-lbc-msgid-slotsp (fn-lbc-msgid-slots-append rec rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-msgid-slots-append{preserved} (fn-lbc-msgid-slots rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-slotsp fn-lbc-msgid-slots-append)))))

(defthm fn-lbc-msgid-octetsp-of-clear
 (implies (fn-lbc-msgid-octetsp rows) (fn-lbc-msgid-octetsp (fn-lbc-msgid-octets-clear rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-msgid-octets-clear{preserved} (fn-lbc-msgid-octets rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-octetsp fn-lbc-msgid-octets-clear fn-lbc-msgid-octets$a-clear)))))

(defthm fn-lbc-overview-octetsp-of-clear
 (implies (fn-lbc-overview-octetsp rows) (fn-lbc-overview-octetsp (fn-lbc-overview-octets-clear rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-overview-octets-clear{preserved} (fn-lbc-overview-octets rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-overview-octetsp fn-lbc-overview-octets-clear fn-lbc-overview-octets$a-clear)))))

(defthm fn-lbc-rowwordsp-of-clear
 (implies (fn-lbc-rowwordsp rows) (fn-lbc-rowwordsp (fn-lbc-rowwords-clear rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-rowwords-clear{preserved} (fn-lbc-rowwords rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-rowwordsp fn-lbc-rowwords-clear fn-lbc-rowwords$a-clear)))))

(defthm fn-lbc-directoryp-of-clear
 (implies (fn-lbc-directoryp rows) (fn-lbc-directoryp (fn-lbc-directory-clear rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-directory-clear{preserved} (fn-lbc-directory rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-directoryp fn-lbc-directory-clear fn-lbc-directory$a-clear)))))

(defthm fn-lbc-membershipsp-of-clear
 (implies (fn-lbc-membershipsp rows) (fn-lbc-membershipsp (fn-lbc-memberships-clear rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-memberships-clear{preserved} (fn-lbc-memberships rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-membershipsp fn-lbc-memberships-clear fn-lbc-memberships$a-clear)))))

(defthm fn-lbc-novp-of-clear
 (implies (fn-lbc-novp rows) (fn-lbc-novp (fn-lbc-nov-clear rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-nov-clear{preserved} (fn-lbc-nov rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-novp fn-lbc-nov-clear fn-lbc-nov$a-clear)))))

(defthm fn-lbc-msgid-slotsp-of-clear
 (implies (fn-lbc-msgid-slotsp rows) (fn-lbc-msgid-slotsp (fn-lbc-msgid-slots-clear rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-msgid-slots-clear{preserved} (fn-lbc-msgid-slots rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-slotsp fn-lbc-msgid-slots-clear fn-lbc-msgid-slots$a-clear)))))

(defthm fn-dmapp-of-put
 (implies (and (fn-dmapp rows) (fn-dm-lanep lane)) (fn-dmapp (fn-dmap-put lane k v rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-dmap-put{preserved} (fn-dmap rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-dmapp fn-dmap-put)))))

(defthm fn-dmapp-of-clear
 (implies (and (fn-dmapp rows) t) (fn-dmapp (fn-dmap-clear  rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-dmap-clear{preserved} (fn-dmap rows)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-dmapp fn-dmap-clear)))))

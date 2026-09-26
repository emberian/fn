/* fn's ML-DSA-65 seam: the vendored PQClean FIPS 204 implementation
 * (third_party/pqclean-ml-dsa-65) plus the exact key-file encodings the
 * node already stores (OpenSSL 3.5's PKCS#8 and SubjectPublicKeyInfo PEM).
 *
 * Part of HST-004's trust boundary, replacing OpenSSL's EVP ML-DSA-65
 * (HST-016).  It owns no policy: ACL2 supplies every signed preimage and
 * makes every acceptance decision; this file signs, verifies, generates and
 * encodes.  Pure ML-DSA with the empty context only, as OpenSSL's
 * EVP_PKEY_sign/verify with "ML-DSA-65" and no parameters.
 *
 * Key files are recognized by exact DER layout, never by a general ASN.1
 * parser (RFC 9881 / draft-ietf-lamps-dilithium-certificates):
 *   public:  SEQUENCE { SEQUENCE { OID 2.16.840.1.101.3.4.3.18 },
 *                       BIT STRING (0 unused bits, 1952 octets) }
 *   private: PKCS#8 v0 PrivateKeyInfo, the same algorithm, whose OCTET
 *            STRING holds one of the three ML-DSA-PrivateKey choices:
 *              seed        [0] IMPLICIT OCTET STRING (32)
 *              expandedKey OCTET STRING (4032)
 *              both        SEQUENCE { seed OCTET STRING (32),
 *                                     expandedKey OCTET STRING (4032) }
 *            OpenSSL 3.5 writes "both" by default; so does this file.
 *            A "both" key whose seed does not regenerate its expanded key
 *            is refused (as OpenSSL's import check does).
 * PEM armor: the BEGIN line first, base64 in lines, the END line, an
 * optional final newline; nothing else.
 *
 * Return codes: 0 success (verify: verified), 1 verify refused, negative a
 * fault (fn_mldsa65_strerror).  A fault is never a verification verdict.
 */

#if defined(__linux__)
#define _DEFAULT_SOURCE 1
#endif

#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>
#if defined(__linux__) || defined(__APPLE__)
#include <sys/random.h>
#endif

#include "api.h"
#include "randombytes.h"

#define FN_EXPORT __attribute__((visibility("default")))

#define PK_OCTETS PQCLEAN_MLDSA65_CLEAN_CRYPTO_PUBLICKEYBYTES   /* 1952 */
#define SK_OCTETS PQCLEAN_MLDSA65_CLEAN_CRYPTO_SECRETKEYBYTES   /* 4032 */
#define SIG_OCTETS PQCLEAN_MLDSA65_CLEAN_CRYPTO_BYTES           /* 3309 */
#define SEED_OCTETS 32
#define PEM_MAX_OCTETS 16384

enum {
    FN_MLDSA65_OK = 0,
    FN_MLDSA65_REFUSED = 1,
    FN_MLDSA65_EARG = -1,
    FN_MLDSA65_EIO = -2,
    FN_MLDSA65_EFILE = -3,
    FN_MLDSA65_EARMOR = -4,
    FN_MLDSA65_EBASE64 = -5,
    FN_MLDSA65_EDER = -6,
    FN_MLDSA65_EINCONSISTENT = -7,
    FN_MLDSA65_EENTROPY = -8,
    FN_MLDSA65_ESPACE = -9,
    FN_MLDSA65_ESIGN = -10
};

#define FN_MLDSA65_UPSTREAM \
    "PQClean ml-dsa-65 clean 0586a824fc0d49df0b6b6e9179d8d15d06d0974f"

/* ------------------------------------------------------------ randomness */

static _Thread_local const uint8_t *fn_injected_seed = NULL;

static int fn_entropy(uint8_t *out, size_t n) {
    while (n > 0) {
        size_t chunk = n > 256 ? 256 : n;
        if (getentropy(out, chunk) != 0) {
            return -1;
        }
        out += chunk;
        n -= chunk;
    }
    return 0;
}

static _Thread_local int fn_entropy_failed = 0;

/* PQClean's randomness hook.  keypair draws its 32-octet seed here and
 * signing draws its 32-octet hedge; an injected seed answers exactly one
 * 32-octet draw. */
int PQCLEAN_randombytes(uint8_t *output, size_t n) {
    if (fn_injected_seed != NULL && n == SEED_OCTETS) {
        memcpy(output, fn_injected_seed, SEED_OCTETS);
        fn_injected_seed = NULL;
        return 0;
    }
    if (fn_entropy(output, n) != 0) {
        /* PQClean ignores this return value; the caller checks the flag. */
        memset(output, 0, n);
        fn_entropy_failed = 1;
        return -1;
    }
    return 0;
}

static void fn_wipe(void *p, size_t n) {
    volatile uint8_t *v = (volatile uint8_t *)p;
    while (n-- > 0) {
        *v++ = 0;
    }
}

/* ------------------------------------------------------------ DER layouts */

static const uint8_t spki_prefix[] = {
    0x30, 0x82, 0x07, 0xb2, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
    0x65, 0x03, 0x04, 0x03, 0x12, 0x03, 0x82, 0x07, 0xa1, 0x00
};
/* PrivateKeyInfo prefixes up to the inner ML-DSA-PrivateKey. */
static const uint8_t pkcs8_both_prefix[] = {
    0x30, 0x82, 0x0f, 0xfe, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60,
    0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12, 0x04, 0x82, 0x0f, 0xea,
    0x30, 0x82, 0x0f, 0xe6, 0x04, 0x20
};
static const uint8_t both_middle[] = { 0x04, 0x82, 0x0f, 0xc0 };
static const uint8_t pkcs8_seed_prefix[] = {
    0x30, 0x34, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48,
    0x01, 0x65, 0x03, 0x04, 0x03, 0x12, 0x04, 0x22, 0x80, 0x20
};
static const uint8_t pkcs8_expanded_prefix[] = {
    0x30, 0x82, 0x0f, 0xd8, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60,
    0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12, 0x04, 0x82, 0x0f, 0xc4,
    0x04, 0x82, 0x0f, 0xc0
};

#define SPKI_OCTETS (sizeof spki_prefix + PK_OCTETS)
#define BOTH_OCTETS (sizeof pkcs8_both_prefix + SEED_OCTETS + \
                     sizeof both_middle + SK_OCTETS)
#define SEED_ONLY_OCTETS (sizeof pkcs8_seed_prefix + SEED_OCTETS)
#define EXPANDED_OCTETS (sizeof pkcs8_expanded_prefix + SK_OCTETS)

/* ------------------------------------------------------------ PEM */

static const char b64_alphabet[] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

static int b64_value(uint8_t c) {
    const char *p;
    if (c == 0) {
        return -1;
    }
    p = strchr(b64_alphabet, (int)c);
    return p == NULL ? -1 : (int)(p - b64_alphabet);
}

static int starts_with(const uint8_t *p, size_t n, const char *s) {
    size_t k = strlen(s);
    return n >= k && memcmp(p, s, k) == 0;
}

/* Decode the PEM armored with LABEL into DER (capacity CAP); *LEN gets the
 * DER length. */
static int pem_decode(const uint8_t *pem, size_t n, const char *label,
                      uint8_t *der, size_t cap, size_t *len) {
    char begin[64], end[64];
    size_t pos, out = 0, pad = 0;
    uint32_t acc = 0;
    int bits = 0;
    if (strlen(label) > 40) {
        return FN_MLDSA65_EARG;
    }
    strcpy(begin, "-----BEGIN ");
    strcat(begin, label);
    strcat(begin, "-----");
    strcpy(end, "-----END ");
    strcat(end, label);
    strcat(end, "-----");
    if (!starts_with(pem, n, begin)) {
        return FN_MLDSA65_EARMOR;
    }
    pos = strlen(begin);
    if (pos < n && pem[pos] == '\r') {
        pos++;
    }
    if (pos >= n || pem[pos] != '\n') {
        return FN_MLDSA65_EARMOR;
    }
    pos++;
    for (;;) {
        uint8_t c;
        if (pos >= n) {
            return FN_MLDSA65_EARMOR;
        }
        c = pem[pos];
        if (c == '-') {
            break;
        }
        if (c == '\n' || c == '\r') {
            pos++;
            continue;
        }
        if (c == '=') {
            pad++;
            pos++;
            continue;
        }
        if (pad > 0) {
            return FN_MLDSA65_EBASE64;
        }
        {
            int v = b64_value(c);
            if (v < 0) {
                return FN_MLDSA65_EBASE64;
            }
            acc = (acc << 6) | (uint32_t)v;
            bits += 6;
            if (bits >= 8) {
                bits -= 8;
                if (out >= cap) {
                    return FN_MLDSA65_EDER;
                }
                der[out++] = (uint8_t)(acc >> bits);
                acc &= (1u << bits) - 1u;
            }
        }
        pos++;
    }
    /* Canonical padding: the leftover bits are zero and the padding
     * completes a quantum. */
    if (acc != 0 || !((bits == 0 && pad == 0) || (bits == 4 && pad == 2) ||
                      (bits == 2 && pad == 1))) {
        return FN_MLDSA65_EBASE64;
    }
    if (!starts_with(pem + pos, n - pos, end)) {
        return FN_MLDSA65_EARMOR;
    }
    pos += strlen(end);
    if (pos < n && pem[pos] == '\r') {
        pos++;
    }
    if (pos < n && pem[pos] == '\n') {
        pos++;
    }
    if (pos != n) {
        return FN_MLDSA65_EARMOR;
    }
    *len = out;
    return FN_MLDSA65_OK;
}

static int pem_encode(const uint8_t *der, size_t n, const char *label,
                      uint8_t *pem, size_t cap, size_t *len) {
    size_t need = 0, out = 0, i, line = 0;
    char begin[64], end[64];
    strcpy(begin, "-----BEGIN ");
    strcat(begin, label);
    strcat(begin, "-----\n");
    strcpy(end, "-----END ");
    strcat(end, label);
    strcat(end, "-----\n");
    need = strlen(begin) + strlen(end) + ((n + 2) / 3) * 4 + ((n + 2) / 3 * 4 + 63) / 64;
    if (need > cap) {
        return FN_MLDSA65_ESPACE;
    }
    memcpy(pem, begin, strlen(begin));
    out = strlen(begin);
    for (i = 0; i < n; i += 3) {
        uint32_t v = (uint32_t)der[i] << 16;
        size_t k = n - i;
        if (k > 1) {
            v |= (uint32_t)der[i + 1] << 8;
        }
        if (k > 2) {
            v |= der[i + 2];
        }
        pem[out++] = (uint8_t)b64_alphabet[(v >> 18) & 63];
        pem[out++] = (uint8_t)b64_alphabet[(v >> 12) & 63];
        pem[out++] = k > 1 ? (uint8_t)b64_alphabet[(v >> 6) & 63] : '=';
        pem[out++] = k > 2 ? (uint8_t)b64_alphabet[v & 63] : '=';
        line += 4;
        if (line == 64) {
            pem[out++] = '\n';
            line = 0;
        }
    }
    if (line != 0) {
        pem[out++] = '\n';
    }
    memcpy(pem + out, end, strlen(end));
    out += strlen(end);
    *len = out;
    return FN_MLDSA65_OK;
}

/* ------------------------------------------------------------ files */

static int read_bounded(const char *path, uint8_t *buf, size_t cap, size_t *len) {
    struct stat st;
    size_t got = 0;
    int fd;
    if (path == NULL || path[0] == 0) {
        return FN_MLDSA65_EARG;
    }
    fd = open(path, O_RDONLY | O_NOFOLLOW);
    if (fd < 0) {
        return FN_MLDSA65_EIO;
    }
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_size < 0 ||
            (unsigned long long)st.st_size > cap) {
        close(fd);
        return FN_MLDSA65_EFILE;
    }
    for (;;) {
        ssize_t r = read(fd, buf + got, cap - got);
        if (r < 0) {
            if (errno == EINTR) {
                continue;
            }
            close(fd);
            return FN_MLDSA65_EIO;
        }
        if (r == 0) {
            break;
        }
        got += (size_t)r;
        if (got == cap) {
            /* One more octet would exceed the bound. */
            uint8_t extra;
            ssize_t more = read(fd, &extra, 1);
            if (more != 0) {
                close(fd);
                return FN_MLDSA65_EFILE;
            }
            break;
        }
    }
    close(fd);
    *len = got;
    return FN_MLDSA65_OK;
}

/* ------------------------------------------------------------ keys */

static int keypair_from_seed(const uint8_t seed[SEED_OCTETS],
                             uint8_t pk[PK_OCTETS], uint8_t sk[SK_OCTETS]) {
    fn_injected_seed = seed;
    PQCLEAN_MLDSA65_CLEAN_crypto_sign_keypair(pk, sk);
    if (fn_injected_seed != NULL) {
        fn_injected_seed = NULL;
        return FN_MLDSA65_ESIGN;
    }
    return FN_MLDSA65_OK;
}

/* Decode a private PEM into SK (and PK when it can be derived: the seed
 * forms).  *HAS_PK says whether PK was filled. */
static int private_from_pem(const uint8_t *pem, size_t n,
                            uint8_t sk[SK_OCTETS], uint8_t pk[PK_OCTETS],
                            int *has_pk) {
    uint8_t der[BOTH_OCTETS + 16];
    uint8_t derived[SK_OCTETS];
    size_t len = 0;
    int rc = pem_decode(pem, n, "PRIVATE KEY", der, sizeof der, &len);
    *has_pk = 0;
    if (rc != FN_MLDSA65_OK) {
        fn_wipe(der, sizeof der);
        return rc;
    }
    if (len == BOTH_OCTETS &&
            memcmp(der, pkcs8_both_prefix, sizeof pkcs8_both_prefix) == 0 &&
            memcmp(der + sizeof pkcs8_both_prefix + SEED_OCTETS, both_middle,
                   sizeof both_middle) == 0) {
        const uint8_t *seed = der + sizeof pkcs8_both_prefix;
        const uint8_t *expanded = seed + SEED_OCTETS + sizeof both_middle;
        rc = keypair_from_seed(seed, pk, derived);
        if (rc == FN_MLDSA65_OK && memcmp(derived, expanded, SK_OCTETS) != 0) {
            rc = FN_MLDSA65_EINCONSISTENT;
        }
        if (rc == FN_MLDSA65_OK) {
            memcpy(sk, derived, SK_OCTETS);
            *has_pk = 1;
        }
    } else if (len == SEED_ONLY_OCTETS &&
               memcmp(der, pkcs8_seed_prefix, sizeof pkcs8_seed_prefix) == 0) {
        rc = keypair_from_seed(der + sizeof pkcs8_seed_prefix, pk, sk);
        *has_pk = rc == FN_MLDSA65_OK;
    } else if (len == EXPANDED_OCTETS &&
               memcmp(der, pkcs8_expanded_prefix,
                      sizeof pkcs8_expanded_prefix) == 0) {
        memcpy(sk, der + sizeof pkcs8_expanded_prefix, SK_OCTETS);
        rc = FN_MLDSA65_OK;
    } else {
        rc = FN_MLDSA65_EDER;
    }
    fn_wipe(der, sizeof der);
    fn_wipe(derived, sizeof derived);
    return rc;
}

/* ------------------------------------------------------------ exported */

FN_EXPORT const char *fn_mldsa65_implementation(void) {
    return FN_MLDSA65_UPSTREAM;
}

/* Widths this library was built for: public key, signature, secret key. */
FN_EXPORT int fn_mldsa65_widths(size_t out[3]) {
    if (out == NULL) {
        return FN_MLDSA65_EARG;
    }
    out[0] = PK_OCTETS;
    out[1] = SIG_OCTETS;
    out[2] = SK_OCTETS;
    return FN_MLDSA65_OK;
}

FN_EXPORT const char *fn_mldsa65_strerror(int code) {
    switch (code) {
    case FN_MLDSA65_OK: return "ok";
    case FN_MLDSA65_REFUSED: return "signature refused";
    case FN_MLDSA65_EARG: return "invalid argument";
    case FN_MLDSA65_EIO: return "cannot open or read the key file";
    case FN_MLDSA65_EFILE: return "key file is not a regular file within 16384 octets";
    case FN_MLDSA65_EARMOR: return "not a PEM with the expected armor";
    case FN_MLDSA65_EBASE64: return "PEM body is not canonical base64";
    case FN_MLDSA65_EDER: return "not an ML-DSA-65 key in a recognized encoding";
    case FN_MLDSA65_EINCONSISTENT: return "private key seed does not generate its expanded key";
    case FN_MLDSA65_EENTROPY: return "the operating system's entropy source failed";
    case FN_MLDSA65_ESPACE: return "output buffer too small";
    case FN_MLDSA65_ESIGN: return "ML-DSA-65 primitive failed";
    default: return "unknown ML-DSA-65 seam code";
    }
}

FN_EXPORT int fn_mldsa65_public_from_pem(const uint8_t *pem, size_t n,
        uint8_t pk[PK_OCTETS]) {
    uint8_t der[SPKI_OCTETS + 16];
    size_t len = 0;
    int rc;
    if (pem == NULL || pk == NULL) {
        return FN_MLDSA65_EARG;
    }
    rc = pem_decode(pem, n, "PUBLIC KEY", der, sizeof der, &len);
    if (rc != FN_MLDSA65_OK) {
        return rc;
    }
    if (len != SPKI_OCTETS || memcmp(der, spki_prefix, sizeof spki_prefix) != 0) {
        return FN_MLDSA65_EDER;
    }
    memcpy(pk, der + sizeof spki_prefix, PK_OCTETS);
    return FN_MLDSA65_OK;
}

FN_EXPORT int fn_mldsa65_public_from_pem_file(const char *path,
        uint8_t pk[PK_OCTETS]) {
    uint8_t buf[PEM_MAX_OCTETS];
    size_t n = 0;
    int rc = read_bounded(path, buf, sizeof buf, &n);
    if (rc != FN_MLDSA65_OK) {
        return rc;
    }
    return fn_mldsa65_public_from_pem(buf, n, pk);
}

/* The public key a private PEM determines (seed forms only). */
FN_EXPORT int fn_mldsa65_public_from_private_pem(const uint8_t *pem, size_t n,
        uint8_t pk[PK_OCTETS]) {
    uint8_t sk[SK_OCTETS];
    int has_pk = 0;
    int rc;
    if (pem == NULL || pk == NULL) {
        return FN_MLDSA65_EARG;
    }
    rc = private_from_pem(pem, n, sk, pk, &has_pk);
    fn_wipe(sk, sizeof sk);
    if (rc == FN_MLDSA65_OK && !has_pk) {
        rc = FN_MLDSA65_EDER;
    }
    return rc;
}

/* Pure ML-DSA-65, empty context, hedged. */
FN_EXPORT int fn_mldsa65_sign_pem(const uint8_t *pem, size_t n,
                                  const uint8_t *m, size_t mlen,
                                  uint8_t sig[SIG_OCTETS]) {
    uint8_t sk[SK_OCTETS], pk[PK_OCTETS];
    size_t siglen = 0;
    int has_pk = 0;
    int rc;
    if (pem == NULL || sig == NULL || (m == NULL && mlen != 0)) {
        return FN_MLDSA65_EARG;
    }
    rc = private_from_pem(pem, n, sk, pk, &has_pk);
    if (rc == FN_MLDSA65_OK) {
        fn_entropy_failed = 0;
        if (PQCLEAN_MLDSA65_CLEAN_crypto_sign_signature(sig, &siglen, m, mlen, sk) != 0 ||
                siglen != SIG_OCTETS) {
            rc = FN_MLDSA65_ESIGN;
        } else if (fn_entropy_failed) {
            rc = FN_MLDSA65_EENTROPY;
        }
        if (rc != FN_MLDSA65_OK) {
            fn_wipe(sig, SIG_OCTETS);
        }
    }
    fn_wipe(sk, sizeof sk);
    return rc;
}

FN_EXPORT int fn_mldsa65_sign_pem_file(const char *path,
                                       const uint8_t *m, size_t mlen,
                                       uint8_t sig[SIG_OCTETS]) {
    uint8_t buf[PEM_MAX_OCTETS];
    size_t n = 0;
    int rc = read_bounded(path, buf, sizeof buf, &n);
    if (rc == FN_MLDSA65_OK) {
        rc = fn_mldsa65_sign_pem(buf, n, m, mlen, sig);
    }
    fn_wipe(buf, sizeof buf);
    return rc;
}

/* 0 verified, 1 refused (including a wrong signature width). */
FN_EXPORT int fn_mldsa65_verify(const uint8_t *sig, size_t siglen,
                                const uint8_t *m, size_t mlen,
                                const uint8_t pk[PK_OCTETS]) {
    if (sig == NULL || pk == NULL || (m == NULL && mlen != 0)) {
        return FN_MLDSA65_EARG;
    }
    if (siglen != SIG_OCTETS) {
        return FN_MLDSA65_REFUSED;
    }
    return PQCLEAN_MLDSA65_CLEAN_crypto_sign_verify(sig, siglen, m, mlen, pk) == 0
           ? FN_MLDSA65_OK : FN_MLDSA65_REFUSED;
}

/* The key pair a 32-octet seed determines (FIPS 204 ML-DSA.KeyGen_internal),
 * as the PEMs OpenSSL 3.5 writes by default. */
FN_EXPORT int fn_mldsa65_pem_from_seed(const uint8_t seed[SEED_OCTETS],
                                       uint8_t *priv, size_t priv_cap, size_t *priv_len,
                                       uint8_t *pub, size_t pub_cap, size_t *pub_len) {
    uint8_t pk[PK_OCTETS], sk[SK_OCTETS];
    uint8_t der[BOTH_OCTETS];
    uint8_t spki[SPKI_OCTETS];
    int rc;
    if (seed == NULL || priv == NULL || priv_len == NULL || pub == NULL || pub_len == NULL) {
        return FN_MLDSA65_EARG;
    }
    rc = keypair_from_seed(seed, pk, sk);
    if (rc == FN_MLDSA65_OK) {
        size_t at = 0;
        memcpy(der, pkcs8_both_prefix, sizeof pkcs8_both_prefix);
        at = sizeof pkcs8_both_prefix;
        memcpy(der + at, seed, SEED_OCTETS);
        at += SEED_OCTETS;
        memcpy(der + at, both_middle, sizeof both_middle);
        at += sizeof both_middle;
        memcpy(der + at, sk, SK_OCTETS);
        memcpy(spki, spki_prefix, sizeof spki_prefix);
        memcpy(spki + sizeof spki_prefix, pk, PK_OCTETS);
        rc = pem_encode(der, sizeof der, "PRIVATE KEY", priv, priv_cap, priv_len);
        if (rc == FN_MLDSA65_OK) {
            rc = pem_encode(spki, sizeof spki, "PUBLIC KEY", pub, pub_cap, pub_len);
        }
        if (rc != FN_MLDSA65_OK) {
            fn_wipe(priv, priv_cap);
        }
    }
    fn_wipe(sk, sizeof sk);
    fn_wipe(der, sizeof der);
    return rc;
}

/* A fresh pair from the operating system's entropy. */
FN_EXPORT int fn_mldsa65_generate_pem(uint8_t *priv, size_t priv_cap, size_t *priv_len,
                                      uint8_t *pub, size_t pub_cap, size_t *pub_len) {
    uint8_t seed[SEED_OCTETS];
    int rc;
    if (fn_entropy(seed, sizeof seed) != 0) {
        return FN_MLDSA65_EENTROPY;
    }
    rc = fn_mldsa65_pem_from_seed(seed, priv, priv_cap, priv_len, pub, pub_cap, pub_len);
    fn_wipe(seed, sizeof seed);
    return rc;
}

/* Physical TLS primitive. No socket, NNTP, identity, admission or time policy.
 * Callers supply profile-sized BIO capacity and bounded byte spans. */
#include <limits.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/ssl.h>
#include <openssl/x509.h>
#include <openssl/x509v3.h>

#if !defined(OPENSSL_VERSION_MAJOR) || OPENSSL_VERSION_MAJOR != 3
#error "fn2 TLS primitive requires OpenSSL 3"
#endif

/* ABI outcomes: progress, needs input, needs output, peer closed, failed. */
enum { FN2_TLS_OK, FN2_TLS_READ, FN2_TLS_WRITE, FN2_TLS_CLOSED, FN2_TLS_FAILED };
struct fn2_tls { SSL *ssl; BIO *wire; };

/* Configuration must never prompt on the node's stdin. Encrypted keys need
 * an explicit future secret-provider interface; this profile refuses them. */
static int fn2_tls_no_passphrase(char *buffer, int size, int writing, void *data)
{
    (void)buffer; (void)size; (void)writing; (void)data;
    return 0;
}

void *fn2_tls_config(const char *certificate, const char *key, int minimum_version)
{
    SSL_CTX *ctx;
    if (!certificate || !key) return NULL;
    ERR_clear_error();
    ctx = SSL_CTX_new(TLS_server_method());
    if (!ctx) return NULL;
    SSL_CTX_set_default_passwd_cb(ctx, fn2_tls_no_passphrase);
    if (!SSL_CTX_set_min_proto_version(ctx, minimum_version) ||
        SSL_CTX_use_certificate_chain_file(ctx, certificate) != 1 ||
        SSL_CTX_use_PrivateKey_file(ctx, key, SSL_FILETYPE_PEM) != 1 ||
        SSL_CTX_check_private_key(ctx) != 1) {
        SSL_CTX_free(ctx);
        return NULL;
    }
    /* Renegotiation and early application data have no admitted machine state. */
    SSL_CTX_set_options(ctx, SSL_OP_NO_RENEGOTIATION);
    SSL_CTX_set_max_early_data(ctx, 0);
    SSL_CTX_set_session_cache_mode(ctx, SSL_SESS_CACHE_OFF);
    return ctx;
}

void *fn2_tls_server_config_mtls(const char *certificate, const char *key,
                                 const char *client_ca_file, int verify_client,
                                 int minimum_version)
{
    SSL_CTX *ctx = fn2_tls_config(certificate, key, minimum_version);
    int mode;
    if (!ctx) return NULL;
    if (client_ca_file && client_ca_file[0] != '\0') {
        if (SSL_CTX_load_verify_locations(ctx, client_ca_file, NULL) != 1) {
            SSL_CTX_free(ctx);
            return NULL;
        }
    }
    if (verify_client > 0) {
        mode = SSL_VERIFY_PEER;
        if (verify_client >= 2) mode |= SSL_VERIFY_FAIL_IF_NO_PEER_CERT;
        SSL_CTX_set_verify(ctx, mode, NULL);
    }
    return ctx;
}

void fn2_tls_config_free(void *ctx) { SSL_CTX_free(ctx); }

void *fn2_tls_client_config(const char *ca_file, int verify_peer, int minimum_version)
{
    SSL_CTX *ctx;
    ERR_clear_error();
    ctx = SSL_CTX_new(TLS_client_method());
    if (!ctx) return NULL;
    SSL_CTX_set_default_passwd_cb(ctx, fn2_tls_no_passphrase);
    if (!SSL_CTX_set_min_proto_version(ctx, minimum_version)) {
        SSL_CTX_free(ctx);
        return NULL;
    }
    SSL_CTX_set_options(ctx, SSL_OP_NO_RENEGOTIATION);
    SSL_CTX_set_max_early_data(ctx, 0);
    SSL_CTX_set_session_cache_mode(ctx, SSL_SESS_CACHE_OFF);
    if (ca_file && ca_file[0] != '\0') {
        if (SSL_CTX_load_verify_locations(ctx, ca_file, NULL) != 1) {
            SSL_CTX_free(ctx);
            return NULL;
        }
    } else if (verify_peer) {
        if (SSL_CTX_set_default_verify_paths(ctx) != 1) {
            SSL_CTX_free(ctx);
            return NULL;
        }
    }
    SSL_CTX_set_verify(ctx, verify_peer ? SSL_VERIFY_PEER : SSL_VERIFY_NONE, NULL);
    return ctx;
}

int fn2_tls_ctx_use_client_credentials(void *config, const char *certificate, const char *key)
{
    SSL_CTX *ctx = config;
    if (!ctx || !certificate || !key) return 0;
    ERR_clear_error();
    if (SSL_CTX_use_certificate_chain_file(ctx, certificate) != 1 ||
        SSL_CTX_use_PrivateKey_file(ctx, key, SSL_FILETYPE_PEM) != 1 ||
        SSL_CTX_check_private_key(ctx) != 1) {
        return 0;
    }
    return 1;
}

void fn2_tls_free(void *state)
{
    struct fn2_tls *tls = state;
    if (!tls) return;
    SSL_free(tls->ssl);
    BIO_free(tls->wire);
    free(tls);
}

static struct fn2_tls *fn2_tls_alloc(void *config, size_t capacity)
{
    struct fn2_tls *tls;
    BIO *inner = NULL, *wire = NULL;
    if (!config || !capacity || capacity > INT_MAX) return NULL;
    tls = calloc(1, sizeof(*tls));
    if (!tls) return NULL;
    ERR_clear_error();
    tls->ssl = SSL_new(config);
    if (!tls->ssl || BIO_new_bio_pair(&inner, capacity, &wire, capacity) != 1) {
        SSL_free(tls->ssl);
        free(tls);
        return NULL;
    }
    SSL_set_bio(tls->ssl, inner, inner); /* SSL owns inner; tls owns wire. */
    /* The immutable pool loan may move between pinned SBCL calls. */
    SSL_set_mode(tls->ssl, SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER);
    tls->wire = wire;
    return tls;
}

void *fn2_tls_new(void *config, size_t capacity)
{
    struct fn2_tls *tls = fn2_tls_alloc(config, capacity);
    if (!tls) return NULL;
    SSL_set_accept_state(tls->ssl);
    return tls;
}

void *fn2_tls_new_client(void *config, size_t capacity, const char *server_name, const char *verify_host)
{
    struct fn2_tls *tls = fn2_tls_alloc(config, capacity);
    if (!tls) return NULL;
    SSL_set_connect_state(tls->ssl);
    if (server_name && server_name[0] != '\0') {
        if (SSL_set_tlsext_host_name(tls->ssl, server_name) != 1) {
            fn2_tls_free(tls);
            return NULL;
        }
    }
    if (verify_host && verify_host[0] != '\0') {
        X509_VERIFY_PARAM *param = SSL_get0_param(tls->ssl);
        if (!param) {
            fn2_tls_free(tls);
            return NULL;
        }
        if (X509_VERIFY_PARAM_set1_ip_asc(param, verify_host) != 1) {
            ERR_clear_error();
            X509_VERIFY_PARAM_set_hostflags(param, X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS);
            if (X509_VERIFY_PARAM_set1_host(param, verify_host, 0) != 1) {
                fn2_tls_free(tls);
                return NULL;
            }
        }
    }
    return tls;
}

static int fn2_tls_outcome(struct fn2_tls *tls, int result)
{
    switch (SSL_get_error(tls->ssl, result)) {
    case SSL_ERROR_WANT_READ: return FN2_TLS_READ;
    case SSL_ERROR_WANT_WRITE: return FN2_TLS_WRITE;
    case SSL_ERROR_ZERO_RETURN: return FN2_TLS_CLOSED;
    default: return FN2_TLS_FAILED;
    }
}

int fn2_tls_handshake(void *state)
{
    struct fn2_tls *tls = state;
    int result;
    if (!tls) return FN2_TLS_FAILED;
    ERR_clear_error();
    result = SSL_do_handshake(tls->ssl);
    return result == 1 ? FN2_TLS_OK : fn2_tls_outcome(tls, result);
}

/* Feed/drain never consume or produce more than the passed span; zero means
 * blocked. Negative means invalid input or a physical BIO failure. */
int fn2_tls_feed(void *state, const void *bytes, size_t length)
{
    struct fn2_tls *tls = state;
    int n;
    if (!tls || length > INT_MAX || (length && !bytes)) return -1;
    if (!length) return 0;
    ERR_clear_error();
    n = BIO_write(tls->wire, bytes, (int)length);
    return n > 0 ? n : (BIO_should_retry(tls->wire) ? 0 : -1);
}
int fn2_tls_drain(void *state, void *bytes, size_t length)
{
    struct fn2_tls *tls = state;
    int n;
    if (!tls || length > INT_MAX || (length && !bytes)) return -1;
    if (!length) return 0;
    ERR_clear_error();
    n = BIO_read(tls->wire, bytes, (int)length);
    return n > 0 ? n : (BIO_should_retry(tls->wire) ? 0 : -1);
}
size_t fn2_tls_output_pending(void *state)
{
    struct fn2_tls *tls = state;
    return tls ? BIO_ctrl_pending(tls->wire) : 0;
}
size_t fn2_tls_input_room(void *state)
{
    struct fn2_tls *tls = state;
    return tls ? BIO_ctrl_get_write_guarantee(tls->wire) : 0;
}

int fn2_tls_read(void *state, void *bytes, size_t length, size_t *count)
{
    struct fn2_tls *tls = state;
    int n;
    if (!count) return FN2_TLS_FAILED;
    *count = 0;
    if (!tls || !bytes || !length || length > INT_MAX) return FN2_TLS_FAILED;
    ERR_clear_error();
    n = SSL_read(tls->ssl, bytes, (int)length);
    if (n <= 0) return fn2_tls_outcome(tls, n);
    *count = (size_t)n;
    return FN2_TLS_OK;
}
int fn2_tls_write(void *state, const void *bytes, size_t length, size_t *count)
{
    struct fn2_tls *tls = state;
    int n;
    if (!count) return FN2_TLS_FAILED;
    *count = 0;
    if (!tls || !bytes || !length || length > INT_MAX) return FN2_TLS_FAILED;
    ERR_clear_error();
    n = SSL_write(tls->ssl, bytes, (int)length);
    if (n <= 0) return fn2_tls_outcome(tls, n);
    *count = (size_t)n;
    return FN2_TLS_OK;
}

int fn2_tls_verify_result(void *state, long *verify_err)
{
    struct fn2_tls *tls = state;
    X509 *cert;
    long err;
    if (!tls) return -1;
    err = SSL_get_verify_result(tls->ssl);
    if (verify_err) *verify_err = err;
    cert = SSL_get1_peer_certificate(tls->ssl);
    if (!cert) return 0;
    X509_free(cert);
    return err == X509_V_OK ? 1 : 0;
}

int fn2_tls_peer_cert_sha256(void *state, unsigned char *out, size_t out_cap)
{
    struct fn2_tls *tls = state;
    X509 *cert;
    unsigned int md_len = 0;
    int ok;
    if (!tls || !out || out_cap < 32) return -1;
    ERR_clear_error();
    cert = SSL_get1_peer_certificate(tls->ssl);
    if (!cert) return 0;
    ok = X509_digest(cert, EVP_sha256(), out, &md_len);
    X509_free(cert);
    if (ok != 1 || md_len != 32) return -1;
    return 32;
}

int fn2_tls_peer_spki_sha256(void *state, unsigned char *out, size_t out_cap)
{
    struct fn2_tls *tls = state;
    X509 *cert;
    X509_PUBKEY *pk;
    unsigned char *der = NULL;
    int der_len;
    unsigned int md_len = 0;
    int ok;
    if (!tls || !out || out_cap < 32) return -1;
    ERR_clear_error();
    cert = SSL_get1_peer_certificate(tls->ssl);
    if (!cert) return 0;
    pk = X509_get_X509_PUBKEY(cert);
    if (!pk) {
        X509_free(cert);
        return -1;
    }
    der_len = i2d_X509_PUBKEY(pk, &der);
    X509_free(cert);
    if (der_len <= 0 || !der) {
        OPENSSL_free(der);
        return -1;
    }
    ok = EVP_Digest(der, (size_t)der_len, out, &md_len, EVP_sha256(), NULL);
    OPENSSL_free(der);
    if (ok != 1 || md_len != 32) return -1;
    return 32;
}

int fn2_tls_peer_spki_der(void *state, unsigned char *out, size_t out_cap)
{
    struct fn2_tls *tls = state;
    X509 *cert;
    X509_PUBKEY *pk;
    unsigned char *der = NULL;
    int der_len;
    if (!tls || out_cap > INT_MAX || (out_cap && !out)) return -1;
    ERR_clear_error();
    cert = SSL_get1_peer_certificate(tls->ssl);
    if (!cert) return 0;
    pk = X509_get_X509_PUBKEY(cert);
    if (!pk) {
        X509_free(cert);
        return -1;
    }
    der_len = i2d_X509_PUBKEY(pk, &der);
    X509_free(cert);
    if (der_len <= 0 || !der) {
        OPENSSL_free(der);
        return -1;
    }
    if (!out && out_cap == 0) {
        OPENSSL_free(der);
        return der_len;
    }
    if ((size_t)der_len > out_cap) {
        OPENSSL_free(der);
        return -1;
    }
    memcpy(out, der, (size_t)der_len);
    OPENSSL_free(der);
    return der_len;
}

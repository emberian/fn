"""End-to-end verification of native host effectors: OS CSPRNG entropy,
nonblocking IPv4/IPv6 outbound connect, dual client/server OpenSSL 3 TLS,
peer certificate/SPKI SHA-256 pinning, and raw-host guard/binding checks.
"""
import ctypes
import hashlib
import os
import platform
import shutil
import socket
import ssl
import subprocess
import sys
import tempfile
import threading
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

FN2_TLS_OK = 0
FN2_TLS_READ = 1
FN2_TLS_WRITE = 2
FN2_TLS_CLOSED = 3
FN2_TLS_FAILED = 4


def _find_tls_library():
    env = os.environ.get("FN2_TLS_LIBRARY")
    if env:
        return Path(env)
    suffix = ".dylib" if platform.system() == "Darwin" else ".so"
    candidate = ROOT / "build" / "lib" / f"libfn2-tls{suffix}"
    return candidate if candidate.exists() else None


def _find_b3_library():
    env = os.environ.get("FN_B3_LIBRARY")
    if env:
        return Path(env)
    suffix = ".dylib" if platform.system() == "Darwin" else ".so"
    candidate = ROOT / "build" / "lib" / f"libfn-blake3{suffix}"
    return candidate if candidate.exists() else None


def _acl2_launcher():
    launcher = ROOT / "tools" / "acl2"
    return launcher if launcher.exists() else None


def _load_tls_lib(path):
    lib = ctypes.CDLL(str(path))
    vp = ctypes.c_void_p
    sz = ctypes.c_size_t
    cp = ctypes.c_char_p
    up = ctypes.POINTER(ctypes.c_ubyte)

    lib.fn2_tls_config.argtypes = [cp, cp, ctypes.c_int]
    lib.fn2_tls_config.restype = vp
    lib.fn2_tls_server_config_mtls.argtypes = [cp, cp, cp, ctypes.c_int, ctypes.c_int]
    lib.fn2_tls_server_config_mtls.restype = vp
    lib.fn2_tls_config_free.argtypes = [vp]
    lib.fn2_tls_config_free.restype = None

    lib.fn2_tls_client_config.argtypes = [cp, ctypes.c_int, ctypes.c_int]
    lib.fn2_tls_client_config.restype = vp
    lib.fn2_tls_ctx_use_client_credentials.argtypes = [vp, cp, cp]
    lib.fn2_tls_ctx_use_client_credentials.restype = ctypes.c_int

    lib.fn2_tls_new.argtypes = [vp, sz]
    lib.fn2_tls_new.restype = vp
    lib.fn2_tls_new_client.argtypes = [vp, sz, cp, cp]
    lib.fn2_tls_new_client.restype = vp
    lib.fn2_tls_free.argtypes = [vp]
    lib.fn2_tls_free.restype = None

    lib.fn2_tls_handshake.argtypes = [vp]
    lib.fn2_tls_handshake.restype = ctypes.c_int
    lib.fn2_tls_feed.argtypes = [vp, vp, sz]
    lib.fn2_tls_feed.restype = ctypes.c_int
    lib.fn2_tls_drain.argtypes = [vp, vp, sz]
    lib.fn2_tls_drain.restype = ctypes.c_int
    lib.fn2_tls_output_pending.argtypes = [vp]
    lib.fn2_tls_output_pending.restype = sz
    lib.fn2_tls_input_room.argtypes = [vp]
    lib.fn2_tls_input_room.restype = sz
    lib.fn2_tls_read.argtypes = [vp, vp, sz, ctypes.POINTER(sz)]
    lib.fn2_tls_read.restype = ctypes.c_int
    lib.fn2_tls_write.argtypes = [vp, vp, sz, ctypes.POINTER(sz)]
    lib.fn2_tls_write.restype = ctypes.c_int

    lib.fn2_tls_verify_result.argtypes = [vp, ctypes.POINTER(ctypes.c_long)]
    lib.fn2_tls_verify_result.restype = ctypes.c_int
    lib.fn2_tls_peer_cert_sha256.argtypes = [vp, up, sz]
    lib.fn2_tls_peer_cert_sha256.restype = ctypes.c_int
    lib.fn2_tls_peer_spki_sha256.argtypes = [vp, up, sz]
    lib.fn2_tls_peer_spki_sha256.restype = ctypes.c_int
    lib.fn2_tls_peer_spki_der.argtypes = [vp, up, sz]
    lib.fn2_tls_peer_spki_der.restype = ctypes.c_int
    return lib


def _make_ephemeral_cert(dirpath, name, cn, san_dns=None, san_ip=None):
    cert = dirpath / f"{name}.pem"
    key = dirpath / f"{name}.key"
    san_parts = []
    if san_dns:
        san_parts.append(f"DNS:{san_dns}")
    if san_ip:
        san_parts.append(f"IP:{san_ip}")
    san = ",".join(san_parts)
    cmd = [
        "openssl", "req", "-x509", "-newkey", "ec",
        "-pkeyopt", "ec_paramgen_curve:P-256",
        "-nodes", "-sha256", "-days", "2",
        "-subj", f"/CN={cn}",
        "-keyout", str(key), "-out", str(cert),
    ]
    if san:
        cmd.extend(["-addext", f"subjectAltName={san}"])
    subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    cert_der = ssl.PEM_cert_to_DER_cert(cert.read_text(encoding="ascii"))
    cert_sha256 = hashlib.sha256(cert_der).digest()

    pub = subprocess.run(
        ["openssl", "x509", "-in", str(cert), "-pubkey", "-noout"],
        check=True, capture_output=True,
    )
    spki_der = subprocess.run(
        ["openssl", "pkey", "-pubin", "-outform", "DER"],
        input=pub.stdout, check=True, capture_output=True,
    ).stdout
    spki_sha256 = hashlib.sha256(spki_der).digest()
    return cert, key, cert_sha256, spki_sha256, spki_der


def _pump_wire(lib, src, dst):
    moved = 0
    while True:
        pending = lib.fn2_tls_output_pending(src)
        room = lib.fn2_tls_input_room(dst)
        n = min(pending, room, 4096)
        if n <= 0:
            break
        buf = (ctypes.c_ubyte * n)()
        drained = lib.fn2_tls_drain(src, buf, n)
        if drained <= 0:
            break
        fed = lib.fn2_tls_feed(dst, buf, drained)
        assert fed == drained, f"short feed {fed} != {drained}"
        moved += fed
    return moved


def _drive_handshake(lib, srv, cli, limit=64):
    srv_rc = lib.fn2_tls_handshake(srv)
    cli_rc = lib.fn2_tls_handshake(cli)
    for _ in range(limit):
        _pump_wire(lib, cli, srv)
        _pump_wire(lib, srv, cli)
        if srv_rc != FN2_TLS_OK:
            srv_rc = lib.fn2_tls_handshake(srv)
        if cli_rc != FN2_TLS_OK:
            cli_rc = lib.fn2_tls_handshake(cli)
        if srv_rc == FN2_TLS_OK and cli_rc == FN2_TLS_OK:
            _pump_wire(lib, cli, srv)
            _pump_wire(lib, srv, cli)
            return srv_rc, cli_rc
        if srv_rc in (FN2_TLS_CLOSED, FN2_TLS_FAILED) or cli_rc in (FN2_TLS_CLOSED, FN2_TLS_FAILED):
            _pump_wire(lib, cli, srv)
            _pump_wire(lib, srv, cli)
            if srv_rc != FN2_TLS_OK:
                srv_rc = lib.fn2_tls_handshake(srv)
            if cli_rc != FN2_TLS_OK:
                cli_rc = lib.fn2_tls_handshake(cli)
            return srv_rc, cli_rc
    raise AssertionError(f"handshake did not converge: srv={srv_rc}, cli={cli_rc}")


def _send_and_recv(lib, sender, receiver, payload):
    in_buf = (ctypes.c_ubyte * len(payload)).from_buffer_copy(payload)
    written = ctypes.c_size_t(0)
    rc = lib.fn2_tls_write(sender, in_buf, len(payload), ctypes.byref(written))
    assert rc == FN2_TLS_OK and written.value == len(payload), (rc, written.value)
    _pump_wire(lib, sender, receiver)
    out_buf = (ctypes.c_ubyte * len(payload))()
    read_n = ctypes.c_size_t(0)
    rc = lib.fn2_tls_read(receiver, out_buf, len(payload), ctypes.byref(read_n))
    assert rc == FN2_TLS_OK and read_n.value == len(payload), (rc, read_n.value)
    return bytes(out_buf[:read_n.value])


class TestTlsClientServerPrimitive(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        lib_path = _find_tls_library()
        if not lib_path:
            raise unittest.SkipTest("libfn2-tls not built; run host/build-tls.sh build/lib")
        if not shutil.which("openssl"):
            raise unittest.SkipTest("openssl CLI unavailable")
        cls.lib = _load_tls_lib(lib_path)
        cls.tmpdir = tempfile.TemporaryDirectory()
        d = Path(cls.tmpdir.name)
        cls.cert, cls.key, cls.cert_sha, cls.spki_sha, cls.spki_der = _make_ephemeral_cert(
            d, "peer", "peer.example", san_dns="peer.example", san_ip="127.0.0.1"
        )
        cls.cli_cert, cls.cli_key, cls.cli_cert_sha, cls.cli_spki_sha, _ = _make_ephemeral_cert(
            d, "client", "client.example", san_dns="client.example"
        )
        cls.rogue_cert, cls.rogue_key, cls.rogue_cert_sha, cls.rogue_spki_sha, _ = _make_ephemeral_cert(
            d, "rogue", "rogue.example", san_dns="rogue.example", san_ip="127.0.0.1"
        )

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls, "tmpdir"):
            cls.tmpdir.cleanup()

    def test_verified_client_server_handshake_digests_and_payload(self):
        srv_cfg = self.lib.fn2_tls_config(str(self.cert).encode(), str(self.key).encode(), 0x0303)
        cli_cfg = self.lib.fn2_tls_client_config(str(self.cert).encode(), 1, 0x0303)
        self.assertTrue(srv_cfg and cli_cfg)
        srv = cli = None
        try:
            srv = self.lib.fn2_tls_new(srv_cfg, 16384)
            cli = self.lib.fn2_tls_new_client(cli_cfg, 16384, b"peer.example", b"peer.example")
            self.assertTrue(srv and cli)
            srv_rc, cli_rc = _drive_handshake(self.lib, srv, cli)
            self.assertEqual((srv_rc, cli_rc), (FN2_TLS_OK, FN2_TLS_OK))

            verify_err = ctypes.c_long(-1)
            self.assertEqual(self.lib.fn2_tls_verify_result(cli, ctypes.byref(verify_err)), 1)
            self.assertEqual(verify_err.value, 0)

            buf32 = (ctypes.c_ubyte * 32)()
            self.assertEqual(self.lib.fn2_tls_peer_cert_sha256(cli, buf32, 32), 32)
            self.assertEqual(bytes(buf32), self.cert_sha)

            self.assertEqual(self.lib.fn2_tls_peer_spki_sha256(cli, buf32, 32), 32)
            self.assertEqual(bytes(buf32), self.spki_sha)

            der_len = self.lib.fn2_tls_peer_spki_der(cli, None, 0)
            self.assertEqual(der_len, len(self.spki_der))
            der_buf = (ctypes.c_ubyte * der_len)()
            self.assertEqual(self.lib.fn2_tls_peer_spki_der(cli, der_buf, der_len), der_len)
            self.assertEqual(bytes(der_buf), self.spki_der)

            c2s = _send_and_recv(self.lib, cli, srv, b"HELLO XFNC PEER\r\n")
            s2c = _send_and_recv(self.lib, srv, cli, b"200 READY\r\n")
            self.assertEqual(c2s, b"HELLO XFNC PEER\r\n")
            self.assertEqual(s2c, b"200 READY\r\n")
        finally:
            if cli:
                self.lib.fn2_tls_free(cli)
            if srv:
                self.lib.fn2_tls_free(srv)
            self.lib.fn2_tls_config_free(cli_cfg)
            self.lib.fn2_tls_config_free(srv_cfg)

    def test_mutual_tls_both_sides_verify_peer_spki(self):
        srv_cfg = self.lib.fn2_tls_server_config_mtls(
            str(self.cert).encode(), str(self.key).encode(),
            str(self.cli_cert).encode(), 2, 0x0303
        )
        cli_cfg = self.lib.fn2_tls_client_config(str(self.cert).encode(), 1, 0x0303)
        self.assertTrue(srv_cfg and cli_cfg)
        self.assertEqual(
            self.lib.fn2_tls_ctx_use_client_credentials(
                cli_cfg, str(self.cli_cert).encode(), str(self.cli_key).encode()
            ),
            1,
        )
        srv = cli = None
        try:
            srv = self.lib.fn2_tls_new(srv_cfg, 16384)
            cli = self.lib.fn2_tls_new_client(cli_cfg, 16384, b"peer.example", b"peer.example")
            self.assertEqual(_drive_handshake(self.lib, srv, cli), (FN2_TLS_OK, FN2_TLS_OK))
            buf32 = (ctypes.c_ubyte * 32)()
            self.assertEqual(self.lib.fn2_tls_peer_spki_sha256(cli, buf32, 32), 32)
            self.assertEqual(bytes(buf32), self.spki_sha)
            self.assertEqual(self.lib.fn2_tls_peer_spki_sha256(srv, buf32, 32), 32)
            self.assertEqual(bytes(buf32), self.cli_spki_sha)
            self.assertEqual(self.lib.fn2_tls_peer_cert_sha256(srv, buf32, 32), 32)
            self.assertEqual(bytes(buf32), self.cli_cert_sha)
        finally:
            if cli:
                self.lib.fn2_tls_free(cli)
            if srv:
                self.lib.fn2_tls_free(srv)
            self.lib.fn2_tls_config_free(cli_cfg)
            self.lib.fn2_tls_config_free(srv_cfg)

    def test_verified_ip_san_negative_controls_and_lifecycle_stress(self):
        srv_cfg = self.lib.fn2_tls_config(str(self.cert).encode(), str(self.key).encode(), 0x0303)
        rogue_srv_cfg = self.lib.fn2_tls_config(str(self.rogue_cert).encode(), str(self.rogue_key).encode(), 0x0303)
        cli_cfg_v = self.lib.fn2_tls_client_config(str(self.cert).encode(), 1, 0x0303)
        cli_cfg_noverify = self.lib.fn2_tls_client_config(b"", 0, 0x0303)
        self.assertTrue(srv_cfg and rogue_srv_cfg and cli_cfg_v and cli_cfg_noverify)
        try:
            # 1. IP SAN verification works with empty SNI and verify_host="127.0.0.1".
            srv = self.lib.fn2_tls_new(srv_cfg, 16384)
            cli = self.lib.fn2_tls_new_client(cli_cfg_v, 16384, b"", b"127.0.0.1")
            try:
                self.assertEqual(_drive_handshake(self.lib, srv, cli), (FN2_TLS_OK, FN2_TLS_OK))
                err = ctypes.c_long(-1)
                self.assertEqual(self.lib.fn2_tls_verify_result(cli, ctypes.byref(err)), 1)
                self.assertEqual(err.value, 0)
            finally:
                self.lib.fn2_tls_free(cli)
                self.lib.fn2_tls_free(srv)

            # 2. Wrong hostname rejected when verify_peer=1.
            srv = self.lib.fn2_tls_new(srv_cfg, 16384)
            cli = self.lib.fn2_tls_new_client(cli_cfg_v, 16384, b"wrong.example", b"wrong.example")
            try:
                _, cli_rc = _drive_handshake(self.lib, srv, cli)
                self.assertEqual(cli_rc, FN2_TLS_FAILED)
            finally:
                self.lib.fn2_tls_free(cli)
                self.lib.fn2_tls_free(srv)

            # 3. Rogue cert rejected under verified CA config.
            srv = self.lib.fn2_tls_new(rogue_srv_cfg, 16384)
            cli = self.lib.fn2_tls_new_client(cli_cfg_v, 16384, b"peer.example", b"peer.example")
            try:
                _, cli_rc = _drive_handshake(self.lib, srv, cli)
                self.assertEqual(cli_rc, FN2_TLS_FAILED)
            finally:
                self.lib.fn2_tls_free(cli)
                self.lib.fn2_tls_free(srv)

            # 4. Pin/TOFU mode exposes rogue SPKI digest without trusting CA chain.
            srv = self.lib.fn2_tls_new(rogue_srv_cfg, 16384)
            cli = self.lib.fn2_tls_new_client(cli_cfg_noverify, 16384, b"rogue.example", b"")
            try:
                self.assertEqual(_drive_handshake(self.lib, srv, cli), (FN2_TLS_OK, FN2_TLS_OK))
                err = ctypes.c_long(0)
                self.assertEqual(self.lib.fn2_tls_verify_result(cli, ctypes.byref(err)), 0)
                self.assertNotEqual(err.value, 0)
                buf32 = (ctypes.c_ubyte * 32)()
                self.assertEqual(self.lib.fn2_tls_peer_spki_sha256(cli, buf32, 32), 32)
                self.assertEqual(bytes(buf32), self.rogue_spki_sha)
                self.assertNotEqual(bytes(buf32), self.spki_sha)
            finally:
                self.lib.fn2_tls_free(cli)
                self.lib.fn2_tls_free(srv)

            # 5. Repeated handshake + abort/failure lifecycle without leaks.
            for i in range(64):
                srv = self.lib.fn2_tls_new(rogue_srv_cfg if (i % 2) else srv_cfg, 4096)
                cli = self.lib.fn2_tls_new_client(cli_cfg_v, 4096, b"peer.example", b"peer.example")
                try:
                    _, cli_rc = _drive_handshake(self.lib, srv, cli)
                    self.assertEqual(cli_rc, FN2_TLS_FAILED if (i % 2) else FN2_TLS_OK)
                finally:
                    self.lib.fn2_tls_free(cli)
                    self.lib.fn2_tls_free(srv)
        finally:
            self.lib.fn2_tls_config_free(cli_cfg_noverify)
            self.lib.fn2_tls_config_free(cli_cfg_v)
            self.lib.fn2_tls_config_free(rogue_srv_cfg)
            self.lib.fn2_tls_config_free(srv_cfg)


def _start_tcp_echo(family, expected_req, reply_bytes, results):
    sock = socket.socket(family, socket.SOCK_STREAM)
    sock.settimeout(90.0)
    bind_addr = ("127.0.0.1", 0) if family == socket.AF_INET else ("::1", 0)
    sock.bind(bind_addr)
    sock.listen(4)
    port = sock.getsockname()[1]

    def _serve():
        try:
            conn, _ = sock.accept()
            with conn:
                conn.settimeout(30.0)
                buf = b""
                while len(buf) < len(expected_req):
                    chunk = conn.recv(len(expected_req) - len(buf))
                    if not chunk:
                        break
                    buf += chunk
                results.append(buf == expected_req)
                conn.sendall(reply_bytes)
        except OSError:
            pass
        finally:
            sock.close()

    t = threading.Thread(target=_serve, daemon=True)
    t.start()
    return port, sock, t


def _start_tls_server(cert_path, key_path, expected_req, reply_bytes, expect_success, results, post_fail_plain_sink=None):
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    ctx.minimum_version = ssl.TLSVersion.TLSv1_2
    ctx.load_cert_chain(certfile=str(cert_path), keyfile=str(key_path))
    raw = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    raw.settimeout(90.0)
    raw.bind(("127.0.0.1", 0))
    raw.listen(2)
    port = raw.getsockname()[1]

    def _serve():
        try:
            conn, _ = raw.accept()
            with conn:
                conn.settimeout(30.0)
                try:
                    tls = ctx.wrap_socket(conn, server_side=True)
                    try:
                        buf = b""
                        while len(buf) < len(expected_req):
                            chunk = tls.recv(len(expected_req) - len(buf))
                            if not chunk:
                                break
                            buf += chunk
                        if expect_success:
                            results.append(buf == expected_req)
                            if buf == expected_req:
                                tls.sendall(reply_bytes)
                        else:
                            # Pin-mismatch path completes TLS handshake then closes without app data.
                            if post_fail_plain_sink is not None:
                                post_fail_plain_sink.extend(buf)
                            results.append(buf == b"")
                    finally:
                        tls.close()
                except (ssl.SSLError, ConnectionResetError, BrokenPipeError):
                    results.append(not expect_success)
        except OSError:
            pass
        finally:
            raw.close()

    t = threading.Thread(target=_serve, daemon=True)
    t.start()
    return port, raw, t


REQUIRED_LEAF_CERTS = (
    "books/assembly-init",
    "books/core-harvest",
    "books/executor-access",
    "books/device-boundary",
    "books/host-result",
    "books/host-ops",
    "books/host-codec",
    "books/host-compress",
    "books/tls",
    "books/compress",
    "books/boot",
    "books/merkle",
    "books/native-b3-evidence",
)

HOST_BOUNDARY_SCALAR_DEFS = """
(defconst *fn2-host-loopback* #x7f000001)
(defconst *fn2-host-path-max* 103)
(defun fn2-host-listener-pathp (path)
  (declare (xargs :guard t))
  (and (stringp path) (< 1 (length path)) (<= (length path) *fn2-host-path-max*)
       (eql (char path 0) #\\/)
       (not (member (code-char 0) (coerce path 'list)))))
(defun fn2-host-listener-bind (profile)
  (declare (xargs :guard t))
  (let* ((profile (and (alistp profile) profile))
         (address (if (assoc-equal :listener-address profile)
                      (fn2-profile-get :listener-address profile) *fn2-host-loopback*))
         (port (if (assoc-equal :listener-port profile)
                   (fn2-profile-get :listener-port profile) 0))
         (pathp (consp (assoc-equal :listener-path profile)))
         (path (fn2-profile-get :listener-path profile)))
    (cond ((not (unsigned-byte-p 32 address)) (mv :listener-address 0 0 nil))
          ((not (unsigned-byte-p 16 port)) (mv :listener-port 0 0 nil))
          ((and pathp (not (fn2-host-listener-pathp path))) (mv :listener-path 0 0 nil))
          (t (mv :ok address port (and pathp path))))))
(defun fn2-host-tls-settings (profile)
  (declare (xargs :guard t))
  (cond ((not (fn2-tls-profilep profile)) (mv :tls-profile nil nil 0 0 0 0 0))
        ((not (fn2-tls-requested-p profile)) (mv :off nil nil 0 0 0 0 0))
        (t (mv :ok (fn2-profile-get :tls-certificate profile) (fn2-profile-get :tls-key profile)
               (fn2-tls-setting :tls-window 16384 profile) *fn2-tls-io-bytes* *fn2-tls-minimum-version*
               (fn2-codec-seed-capacity profile)
               (fn2-tls-setting :tls-handshake-turns 65536 profile)))))
(defun fn2-host-compress-settings (profile)
  (declare (xargs :guard t))
  (let ((capacity (fn2-codec-seed-capacity profile)))
    (cond ((not (fn2-compress-profilep profile)) (mv :compress-profile 0 0 0 0 0))
          ((not (fn2-profile-get :compress-enabled profile)) (mv :off 0 0 0 0 0))
          ((not (and (posp capacity) (unsigned-byte-p 32 capacity)))
           (mv :compress-profile 0 0 0 0 0))
          (t (mv :ok (fn2-profile-get :compress-input-quantum profile)
                     (fn2-profile-get :compress-output-quantum profile)
                     (fn2-profile-get :compress-expansion-ratio profile)
                     (fn2-profile-get :compress-expansion-burst profile) capacity)))))
(local (in-theory (enable fn2-core-wfp)))
(defun fn2-host-stopped-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-stopped-p fn2-core))
(defun fn2-host-stop-reason (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-stop-reason fn2-core))
(defun fn2-host-stop-details (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv (fn2-core-stop-kind fn2-core) (fn2-core-stop-detail fn2-core)))
(defun fn2-host-idle-deadline (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-idle-deadline fn2-core))
"""


class TestLiveAcl2HostEffectors(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.acl2 = _acl2_launcher()
        cls.tls_lib = _find_tls_library()
        cls.b3_lib = _find_b3_library()
        if not cls.acl2 or platform.system() == "Darwin":
            raise unittest.SkipTest("tools/acl2 Linux runtime required")
        missing = [b for b in REQUIRED_LEAF_CERTS if not (ROOT / f"{b}.cert").exists()]
        if missing:
            raise unittest.SkipTest(f"missing leaf certificates: {missing}")
        if not (cls.tls_lib and cls.b3_lib):
            raise unittest.SkipTest("native shared libraries not built in build/lib")
        if not shutil.which("openssl"):
            raise unittest.SkipTest("openssl CLI unavailable")

    def test_raw_host_guard_and_binding_audit_on_certified_leaves(self):
        import served_host_check

        _, order, findings = served_host_check.inspect(ROOT)
        self.assertEqual(findings, [])
        calls, helpers = served_host_check.entry_names(ROOT, order)
        # Only executor/node-profile umbrella symbols live above the leaf books.
        umbrella_only = {
            "fn2-turn",
            "fn2-init-executor",
            "fn2-boot-start",
            "fn2-boot-status",
            "fn2-host-boot-refusal",
            "fn2-image-profile",
            "fn2-image-create-request",
            "fn2-execution-profilep",
            "fn2-origin-profile-from-text",
            "fn2-article-limit-profile-from-text",
            "fn2-startup-groups-from-text",
            "fn2-profile-storage-fault-model",
        }
        checked_calls = [c for c in calls if c not in umbrella_only]
        includes = "\n".join(f'(include-book "{b}")' for b in REQUIRED_LEAF_CERTS)
        raw_loads = '\n'.join(f'(load "{name}")' for name in order)
        synthetic_prefix = f'(in-package "ACL2")\n{includes}\n{HOST_BOUNDARY_SCALAR_DEFS}\n:q\n{raw_loads}\n'
        program = served_host_check.load_program(
            synthetic_prefix, checked_calls, helpers, served_host_check.NATIVE_REPLACEMENTS
        )
        env = os.environ.copy()
        env["FN2_TLS_LIBRARY"] = str(self.tls_lib)
        env["FN_B3_LIBRARY"] = str(self.b3_lib)
        proc = subprocess.run(
            [str(self.acl2), "--timeout", "90"],
            cwd=str(ROOT),
            env=env,
            input=program,
            text=True,
            capture_output=True,
            timeout=105,
        )
        self.assertEqual(proc.returncode, 0, proc.stdout[-4000:] + proc.stderr[-2000:])
        self.assertIn("FN_SERVED_HOST_LOAD_OK", proc.stdout)

    def test_entropy_connect_and_dual_tls_through_acl2_core(self):
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            cert, key, cert_sha, spki_sha, _ = _make_ephemeral_cert(
                d, "peer", "peer.example", san_dns="peer.example", san_ip="127.0.0.1"
            )
            rogue_cert, rogue_key, _, _, _ = _make_ephemeral_cert(
                d, "rogue", "rogue.example", san_dns="rogue.example", san_ip="127.0.0.1"
            )

            srv_results = []
            pin_fail_sink = bytearray()
            threads = []
            listen_socks = []
            port_v4, s4, t4 = _start_tcp_echo(socket.AF_INET, b"PING-V4\n", b"PONG-V4\n", srv_results)
            threads.append(t4)
            listen_socks.append(s4)

            has_v6 = False
            port_v6 = 0
            if socket.has_ipv6:
                try:
                    port_v6, s6, t6 = _start_tcp_echo(socket.AF_INET6, b"PING-V6\n", b"PONG-V6\n", srv_results)
                    threads.append(t6)
                    listen_socks.append(s6)
                    has_v6 = True
                except OSError:
                    has_v6 = False

            closed_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            closed_sock.bind(("127.0.0.1", 0))
            port_closed = closed_sock.getsockname()[1]
            closed_sock.close()

            port_tls_ok, st1, t_tls_ok = _start_tls_server(
                cert, key, b"HELLO-ACL2-TLS\r\n", b"200 TLS-OK\r\n", True, srv_results
            )
            port_tls_rogue, st2, t_tls_bad = _start_tls_server(
                rogue_cert, rogue_key, b"SHOULD-NOT-SEND\r\n", b"", False, srv_results
            )
            port_tls_pin_bad, st3, t_tls_pin_bad = _start_tls_server(
                rogue_cert, rogue_key, b"LEAKED-PLAIN!!\r\n", b"", False, srv_results,
                post_fail_plain_sink=pin_fail_sink,
            )
            threads.extend([t_tls_ok, t_tls_bad, t_tls_pin_bad])
            listen_socks.extend([st1, st2, st3])

            spki_vec_lisp = "#(" + " ".join(str(b) for b in spki_sha) + ")"
            cert_vec_lisp = "#(" + " ".join(str(b) for b in cert_sha) + ")"
            includes = "\n".join(f'(include-book "{b}")' for b in REQUIRED_LEAF_CERTS)

            driver_script = f"""(in-package "ACL2")
{includes}
{HOST_BOUNDARY_SCALAR_DEFS}
(defun test-issue-connect-core (fn2-core family port w0 w1 w2 w3)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
              (fn2-ops (fn2-core-ops fn2-core))
              (fn2-control (fn2-core-control fn2-core)))
             (code oslot ogen fn2-pool fn2-ops fn2-control)
             (fn2-issue-connect family port w0 w1 w2 w3 1 0 1 0 fn2-pool fn2-ops fn2-control)
    (mv code oslot ogen fn2-core)))
:q
(load "host/b3-native.lisp")
(load "host/ffi.lisp")
(load "host/adapter.lisp")
(handler-case
  (progn

    (defun test-pump-harvest (host core &optional (timeout-ms 25) (max-steps 600))
      (dotimes (i max-steps (error "timeout waiting for fn2-harvest-one"))
        (fn2-n-post-completions host)
        (multiple-value-bind (found oslot ogen cell evkind outcome reason count aux0 aux1 next-core)
            (fn2-harvest-one core)
          (setf core next-core)
          (when found
            (return-from test-pump-harvest
              (values oslot ogen cell evkind outcome reason count aux0 aux1 core))))
        (fn2-n-take host)
        (fn2-n-interests host)
        (when (or (zerop (fn2-nhost-pending host))
                  (fn2-n-tls-work-p host)
                  (fn2-n-entropy-work-p host))
          (fn2-native-mux-wait (fn2-nhost-mux host)
            (if (or (plusp (fn2-nhost-pending host))
                    (fn2-n-tls-work-p host)
                    (fn2-n-entropy-work-p host))
                0 timeout-ms))
          (fn2-n-ready host))))

    (defun test-pump-harvest-two (host core &optional (timeout-ms 25) (max-steps 1000))
      (let ((results nil))
        (dotimes (i max-steps (error "timeout waiting for two completions"))
          (fn2-n-post-completions host)
          (loop
            (multiple-value-bind (found oslot ogen cell evkind outcome reason count aux0 aux1 next-core)
                (fn2-harvest-one core)
              (setf core next-core)
              (unless found (return))
              (push (list oslot ogen cell evkind outcome reason count aux0 aux1) results)
              (when (= (length results) 2)
                (return-from test-pump-harvest-two (values (nreverse results) core)))))
          (fn2-n-take host)
          (fn2-n-interests host)
          (fn2-native-mux-wait (fn2-nhost-mux host)
            (if (or (plusp (fn2-nhost-pending host))
                    (fn2-n-tls-work-p host)
                    (fn2-n-entropy-work-p host))
                0 timeout-ms))
          (fn2-n-ready host))))

    (defun test-open-fd-count ()
      (let ((entries (directory "/proc/self/fd/*" :resolve-symlinks nil)))
        (assert (> (length entries) 3))
        (length entries)))

    (defun test-read-pool-bytes (core pslot pgen n)
      (let ((out (make-array n :element-type '(unsigned-byte 8) :initial-element 0)))
        (dotimes (i n)
          (multiple-value-bind (rc b) (fn2-core-read pslot pgen i 1 0 1 core)
            (assert (eq rc :ok))
            (setf (aref out i) b)))
        (values out core)))

    (defun test-write-pool-string (core pslot pgen s)
      (dotimes (i (length s))
        (multiple-value-bind (wc nc) (fn2-core-write pslot pgen i (char-code (char s i)) 1 0 1 core)
          (assert (eq wc :ok))
          (setf core nc)))
      core)

    (defun test-bytes-to-string (bytes)
      (coerce (loop for b across bytes collect (code-char b)) 'string))

    (defun test-close-cap (host core cap nonce)
      (multiple-value-bind (cc _os _og c1) (fn2-issue-close cap nonce 1 0 1 0 core)
        (declare (ignore _os _og))
        (assert (eq cc :ok))
        (setf core c1)
        (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c2)
            (test-pump-harvest host core)
          (declare (ignore os og cell reason count aux0 aux1))
          (assert (= ev (fn2-terminal-event *fn2-action-close*)))
          (assert (eql outcome *fn2-outcome-done*))
          c2)))

    (let* ((profile (put-assoc-equal :pool-classes '((32 . 64) (8 . 512))
                      (put-assoc-equal :o 32
                        (put-assoc-equal :qa 16
                          (put-assoc-equal :tls-key "{key}"
                            (put-assoc-equal :tls-certificate "{cert}" *fn2-profile-tiny*))))))
           (core (fn2-core-init profile (fn2-n-live-core)))
           (host (fn2-n-open-host profile core))
           (initial-fds (test-open-fd-count))
           (lf (string (code-char 10)))
           (crlf (format nil "~C~C" (code-char 13) (code-char 10))))
      (unwind-protect
        (progn
          ;; 1. OS CSPRNG entropy into ACL2 pool: append-lease after 8-byte prefix + len=300 (>256 chunk) + len=0 + /dev/urandom fallback + clean failure-to-cancelled.
          (multiple-value-bind (rc1 pslot1 pgen1 c1) (fn2-core-reserve 0 1 0 1 core)
            (assert (eq rc1 :ok))
            (setf core c1)
            (dotimes (i 8)
              (multiple-value-bind (wc nc) (fn2-core-write pslot1 pgen1 i #xA5 1 0 1 core)
                (assert (eq wc :ok))
                (setf core nc)))
            (multiple-value-bind (ec _s _g c2) (fn2-issue-entropy pslot1 pgen1 32 1 0 1 0 core)
              (declare (ignore _s _g))
              (assert (eq ec :ok))
              (setf core c2))
            (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c3)
                (test-pump-harvest host core)
              (declare (ignore os og cell aux0 aux1))
              (assert (= ev *fn2-event-entropy-result*))
              (assert (eql outcome *fn2-outcome-done*))
              (assert (eql reason *fn2-reason-none*))
              (assert (= count 32))
              (setf core c3))
            ;; fn2-pool-lease-in leases at [fill, fill+len) = [8, 40): verify [0..7] stayed #xA5 and [8..39] got CSPRNG bytes.
            (multiple-value-bind (e1-with-prefix c4) (test-read-pool-bytes core pslot1 pgen1 40)
              (setf core c4)
              (let ((prefix (subseq e1-with-prefix 0 8))
                    (e1 (subseq e1-with-prefix 8 40)))
                (assert (every (lambda (b) (= b #xA5)) prefix))
                (assert (> (length (remove-duplicates (coerce e1 'list))) 8))
                ;; Multi-chunk 300-byte CSPRNG fill (> 256-byte chunk size) in class 1 (512-byte slot).
                (multiple-value-bind (rc2 pslot2 pgen2 c5) (fn2-core-reserve 1 1 0 1 core)
                  (assert (eq rc2 :ok))
                  (setf core c5)
                  (multiple-value-bind (ec2 _s2 _g2 c6) (fn2-issue-entropy pslot2 pgen2 300 1 0 1 0 core)
                    (declare (ignore _s2 _g2))
                    (assert (eq ec2 :ok))
                    (setf core c6))
                  (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c7)
                      (test-pump-harvest host core)
                    (declare (ignore os og cell reason aux0 aux1))
                    (assert (= ev *fn2-event-entropy-result*))
                    (assert (eql outcome *fn2-outcome-done*))
                    (assert (= count 300))
                    (setf core c7))
                  (multiple-value-bind (e300 c8) (test-read-pool-bytes core pslot2 pgen2 300)
                    (setf core c8)
                    (assert (not (equalp e1 (subseq e300 0 32))))
                    (assert (not (equalp (subseq e300 0 32) (subseq e300 256 288))))))
                ;; Zero-length entropy fill.
                (multiple-value-bind (rc0 pslot0 pgen0 c9) (fn2-core-reserve 0 1 0 1 core)
                  (assert (eq rc0 :ok))
                  (setf core c9)
                  (multiple-value-bind (ec0 _s0 _g0 c10) (fn2-issue-entropy pslot0 pgen0 0 1 0 1 0 core)
                    (declare (ignore _s0 _g0))
                    (assert (eq ec0 :ok))
                    (setf core c10))
                  (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c11)
                      (test-pump-harvest host core)
                    (declare (ignore os og cell reason aux0 aux1))
                    (assert (= ev *fn2-event-entropy-result*))
                    (assert (eql outcome *fn2-outcome-done*))
                    (assert (= count 0))
                    (setf core c11)))
                ;; Verify /dev/urandom fallback directly + no fd leak.
                (let ((ubuf (make-array 48 :element-type '(unsigned-byte 8) :initial-element 0))
                      (fds0 (test-open-fd-count)))
                  (sb-sys:with-pinned-objects (ubuf)
                    (multiple-value-bind (ufilled ustatus _uerr)
                        (fn2-native-urandom-fill (sb-sys:vector-sap ubuf) 48)
                      (declare (ignore _uerr))
                      (assert (and (= ufilled 48) (eq ustatus :ok)))))
                  (assert (> (length (remove-duplicates (coerce ubuf 'list))) 8))
                  (assert (= fds0 (test-open-fd-count))))
                ;; Verify CSPRNG hard failure posts :cancelled (count=0) cleanly with ZERO unhandled CL error and ZERO strays.
                (let ((saved-fn (symbol-function 'fn2-native-entropy))
                      (stray-before (fn2-host-stray core)))
                  (unwind-protect
                       (progn
                         (setf (symbol-function 'fn2-native-entropy)
                               (lambda (sap length) (declare (ignore sap length)) (values 0 :failed 5)))
                         (multiple-value-bind (rcf pslotf pgenf cf1) (fn2-core-reserve 0 1 0 1 core)
                           (assert (eq rcf :ok))
                           (setf core cf1)
                           (multiple-value-bind (ecf _sf _gf cf2) (fn2-issue-entropy pslotf pgenf 16 1 0 1 0 core)
                             (declare (ignore _sf _gf))
                             (assert (eq ecf :ok))
                             (setf core cf2))
                           (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 cf3)
                               (test-pump-harvest host core)
                             (declare (ignore os og cell aux0 aux1))
                             (assert (= ev *fn2-event-entropy-result*))
                             (assert (eql outcome *fn2-outcome-cancelled*))
                             (assert (eql reason *fn2-reason-none*))
                             (assert (= count 0))
                             (assert (= stray-before (fn2-host-stray cf3)))
                             (setf core cf3))))
                    (setf (symbol-function 'fn2-native-entropy) saved-fn)))))
            (format t "PASS_ENTROPY~%"))

          ;; 2. Nonblocking IPv4 outbound connect + send/recv + close.
          (multiple-value-bind (cc _cs _cg c1) (test-issue-connect-core core *fn2-peer-family-inet* {port_v4} #x7f000001 0 0 0)
            (declare (ignore _cs _cg))
            (assert (eq cc :ok))
            (setf core c1))
          (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c2)
              (test-pump-harvest host core)
            (declare (ignore os og cell reason count))
            (assert (= ev *fn2-event-connect-result*))
            (assert (eql outcome *fn2-outcome-done*))
            (setf core c2)
            (let ((cap aux0) (nonce aux1))
              (assert (plusp cap))
              (multiple-value-bind (rc pslot pgen c3) (fn2-core-reserve 0 1 0 1 core)
                (assert (eq rc :ok))
                (setf core (test-write-pool-string c3 pslot pgen (concatenate 'string "PING-V4" lf)))
                (multiple-value-bind (sc _ss _sg c4) (fn2-issue-send cap nonce pslot pgen 0 8 0 1 0 1 0 core)
                  (declare (ignore _ss _sg))
                  (assert (eq sc :ok))
                  (setf core c4))
                (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c5)
                    (test-pump-harvest host core)
                  (declare (ignore os og cell reason aux0 aux1))
                  (assert (= ev (fn2-terminal-event *fn2-action-send*)))
                  (assert (eql outcome *fn2-outcome-done*))
                  (assert (= count 8))
                  (setf core c5)))
              (multiple-value-bind (rc rpslot rpgen c6) (fn2-core-reserve 0 1 0 1 core)
                (assert (eq rc :ok))
                (setf core c6)
                (multiple-value-bind (rvc _rs _rg c7) (fn2-issue-receive cap nonce rpslot rpgen 8 1 0 1 0 core)
                  (declare (ignore _rs _rg))
                  (assert (eq rvc :ok))
                  (setf core c7))
                (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c8)
                    (test-pump-harvest host core)
                  (declare (ignore os og cell reason aux0 aux1))
                  (assert (= ev (fn2-terminal-event *fn2-action-receive*)))
                  (assert (eql outcome *fn2-outcome-done*))
                  (assert (= count 8))
                  (multiple-value-bind (reply c9) (test-read-pool-bytes c8 rpslot rpgen 8)
                    (assert (string= (test-bytes-to-string reply) (concatenate 'string "PONG-V4" lf)))
                    (setf core c9))))
              (setf core (test-close-cap host core cap nonce))
              (format t "PASS_CONNECT_V4~%")))

          ;; 3. Nonblocking IPv6 outbound connect (::1) when available.
          (when {1 if has_v6 else 'nil'}
            (multiple-value-bind (cc _cs _cg c1) (test-issue-connect-core core *fn2-peer-family-inet6* {port_v6} 0 0 0 1)
              (declare (ignore _cs _cg))
              (assert (eq cc :ok))
              (setf core c1))
            (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c2)
                (test-pump-harvest host core)
              (declare (ignore os og cell reason count))
              (assert (= ev *fn2-event-connect-result*))
              (assert (eql outcome *fn2-outcome-done*))
              (setf core c2)
              (let ((cap aux0) (nonce aux1))
                (multiple-value-bind (rc pslot pgen c3) (fn2-core-reserve 0 1 0 1 core)
                  (assert (eq rc :ok))
                  (setf core (test-write-pool-string c3 pslot pgen (concatenate 'string "PING-V6" lf)))
                  (multiple-value-bind (sc _ss _sg c4) (fn2-issue-send cap nonce pslot pgen 0 8 0 1 0 1 0 core)
                    (declare (ignore _ss _sg))
                    (assert (eq sc :ok))
                    (setf core c4))
                  (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c5)
                      (test-pump-harvest host core)
                    (declare (ignore os og cell reason aux0 aux1))
                    (assert (eql outcome *fn2-outcome-done*))
                    (setf core c5)))
                (multiple-value-bind (rc rpslot rpgen c6) (fn2-core-reserve 0 1 0 1 core)
                  (assert (eq rc :ok))
                  (setf core c6)
                  (multiple-value-bind (rvc _rs _rg c7) (fn2-issue-receive cap nonce rpslot rpgen 8 1 0 1 0 core)
                    (declare (ignore _rs _rg))
                    (assert (eq rvc :ok))
                    (setf core c7))
                  (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c8)
                      (test-pump-harvest host core)
                    (declare (ignore os og cell reason count aux0 aux1))
                    (assert (eql outcome *fn2-outcome-done*))
                    (multiple-value-bind (reply c9) (test-read-pool-bytes c8 rpslot rpgen 8)
                      (assert (string= (test-bytes-to-string reply) (concatenate 'string "PONG-V6" lf)))
                      (setf core c9))))
                (setf core (test-close-cap host core cap nonce))
                (format t "PASS_CONNECT_V6~%"))))

          ;; 4. ECONNREFUSED reports *fn2-outcome-failed* + *fn2-reason-refused* with zero fd leaks across 8 attempts.
          (let ((fds-before (test-open-fd-count)))
            (dotimes (trial 8)
              (declare (ignore trial))
              (multiple-value-bind (cc _cs _cg c1) (test-issue-connect-core core *fn2-peer-family-inet* {port_closed} #x7f000001 0 0 0)
                (declare (ignore _cs _cg))
                (assert (eq cc :ok))
                (setf core c1))
              (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c2)
                  (test-pump-harvest host core)
                (declare (ignore os og cell))
                (assert (= ev *fn2-event-connect-result*))
                (assert (eql outcome *fn2-outcome-failed*))
                (assert (eql reason *fn2-reason-refused*))
                (assert (and (zerop count) (zerop aux0) (zerop aux1)))
                (setf core c2)))
            (assert (= fds-before (test-open-fd-count)))
            (format t "PASS_CONNECT_REFUSED~%"))

          ;; 5. Genuine in-progress connect cancellation closes connect-fd cleanly with zero fd leaks.
          (let ((fds-before (test-open-fd-count))
                (saved-conn (symbol-function 'fn2-native-connect)))
            (unwind-protect
                 (progn
                   ;; Force :in-progress on a real socketpair fd to guarantee Cancel hits the live connect-fd path.
                   (setf (symbol-function 'fn2-native-connect)
                         (lambda (family port w0 w1 w2 w3)
                           (declare (ignore family port w0 w1 w2 w3))
                           (multiple-value-bind (fd err) (fn2-native-syscall (%fn2-native-socket 2 1 0))
                             (assert (>= fd 0) () "socket failed ~d" err)
                             (fn2-native-configure-socket fd)
                             (values fd :in-progress 0))))
                   (multiple-value-bind (cc cslot cgen c1)
                       (test-issue-connect-core core *fn2-peer-family-inet* {port_closed} #x7f000001 0 0 0)
                     (assert (eq cc :ok))
                     (setf core c1)
                     (fn2-n-take host)
                     (fn2-n-interests host)
                     ;; Verify fd is actually open before Cancel!
                     (assert (= (test-open-fd-count) (1+ fds-before)))
                     (multiple-value-bind (kc _ks _kg c2) (fn2-issue-cancel cslot cgen 1 0 1 0 core)
                       (declare (ignore _ks _kg))
                       (assert (eq kc :ok))
                       (setf core c2))
                     (multiple-value-bind (pair c3) (test-pump-harvest-two host core)
                       (setf core c3)
                       (let ((conn-ev (find *fn2-event-connect-result* pair :key #'fourth))
                             (canc-ev (find *fn2-event-cancel-result* pair :key #'fourth)))
                         (assert (and conn-ev canc-ev))
                         (assert (eql (fifth conn-ev) *fn2-outcome-cancelled*))
                         (assert (eql (fifth canc-ev) *fn2-outcome-done*))))))
              (setf (symbol-function 'fn2-native-connect) saved-conn))
            (assert (= fds-before (test-open-fd-count)))
            (format t "PASS_CONNECT_CANCEL~%"))

          ;; 6. Dual live ACL2 Client <-> ACL2 Server TLS handshake + SPKI/Cert pins + bidirectional encrypted transfer!
          (let ((lport (fn2-nhost-listen-port host)))
            (multiple-value-bind (ac _as _ag c1) (fn2-issue-accept 0 0 1 0 1 0 core)
              (declare (ignore _as _ag))
              (assert (eq ac :ok))
              (setf core c1))
            (multiple-value-bind (cc _cs _cg c2)
                (test-issue-connect-core core *fn2-peer-family-inet* lport #x7f000001 0 0 0)
              (declare (ignore _cs _cg))
              (assert (eq cc :ok))
              (setf core c2))
            (multiple-value-bind (pair c3) (test-pump-harvest-two host core)
              (setf core c3)
              (let* ((acc-ev (find *fn2-event-accept-result* pair :key #'fourth))
                     (con-ev (find *fn2-event-connect-result* pair :key #'fourth))
                     (srv-cap (eighth acc-ev)) (srv-nonce (ninth acc-ev))
                     (cli-cap (eighth con-ev)) (cli-nonce (ninth con-ev))
                     (cli-rec (aref (fn2-nhost-caps host) cli-cap))
                     (srv-rec (aref (fn2-nhost-caps host) srv-cap)))
                (assert (and acc-ev con-ev))
                (assert (and (eql (fifth acc-ev) *fn2-outcome-done*)
                             (eql (fifth con-ev) *fn2-outcome-done*)))
                (fn2-n-configure-cap-client-tls host cli-rec :outbound t
                                                :server-name "peer.example"
                                                :verify-host "peer.example"
                                                :expected-spki {spki_vec_lisp}
                                                :expected-cert-sha256 {cert_vec_lisp}
                                                :ca-file "{cert}" :verify-peer t)
                (multiple-value-bind (rc1 ps1 pg1 c4) (fn2-core-reserve 0 1 0 1 core)
                  (assert (eq rc1 :ok))
                  (multiple-value-bind (rc2 ps2 pg2 c5) (fn2-core-reserve 0 1 0 1 c4)
                    (assert (eq rc2 :ok))
                    (multiple-value-bind (ts1 _1 _2 c6) (fn2-issue-tls-start srv-cap srv-nonce ps1 pg1 0 0 1 0 1 0 c5)
                      (declare (ignore _1 _2))
                      (assert (eq ts1 :ok))
                      (multiple-value-bind (ts2 _3 _4 c7) (fn2-issue-tls-start cli-cap cli-nonce ps2 pg2 0 0 1 0 1 0 c6)
                        (declare (ignore _3 _4))
                        (assert (eq ts2 :ok))
                        (multiple-value-bind (hs-pair c8) (test-pump-harvest-two host c7)
                          (setf core c8)
                          (dolist (ev hs-pair)
                            (assert (= (fourth ev) *fn2-event-tls-result*))
                            (assert (eql (fifth ev) *fn2-outcome-done*))))))))
                ;; Verify client TLS verified status & digests on live handle.
                (multiple-value-bind (vok verr) (fn2-native-tls-verify-status (fn2-ncap-tls cli-rec))
                  (assert (and vok (zerop verr))))
                (assert (equalp (fn2-native-tls-peer-digest (fn2-ncap-tls cli-rec) :spki) {spki_vec_lisp}))
                (assert (equalp (fn2-native-tls-peer-digest (fn2-ncap-tls cli-rec) :cert) {cert_vec_lisp}))
                (assert (null (fn2-native-tls-peer-digest (fn2-ncap-tls srv-rec) :spki)))
                ;; Client -> Server encrypted transfer via ACL2 pool.
                (multiple-value-bind (rc tx-s tx-g c9) (fn2-core-reserve 0 1 0 1 core)
                  (assert (eq rc :ok))
                  (setf core (test-write-pool-string c9 tx-s tx-g (concatenate 'string "DUAL-C2S" crlf)))
                  (multiple-value-bind (rc rx-s rx-g c10) (fn2-core-reserve 0 1 0 1 core)
                    (assert (eq rc :ok))
                    (multiple-value-bind (sc _1 _2 c11) (fn2-issue-send cli-cap cli-nonce tx-s tx-g 0 10 0 1 0 1 0 c10)
                      (declare (ignore _1 _2))
                      (assert (eq sc :ok))
                      (multiple-value-bind (rvc _3 _4 c12) (fn2-issue-receive srv-cap srv-nonce rx-s rx-g 10 1 0 1 0 c11)
                        (declare (ignore _3 _4))
                        (assert (eq rvc :ok))
                        (multiple-value-bind (io-pair c13) (test-pump-harvest-two host c12)
                          (dolist (ev io-pair)
                            (assert (eql (fifth ev) *fn2-outcome-done*))
                            (assert (= (seventh ev) 10)))
                          (multiple-value-bind (got c14) (test-read-pool-bytes c13 rx-s rx-g 10)
                            (assert (string= (test-bytes-to-string got) (concatenate 'string "DUAL-C2S" crlf)))
                            (setf core c14)))))))
                ;; Server -> Client encrypted transfer via ACL2 pool.
                (multiple-value-bind (rc tx-s tx-g c15) (fn2-core-reserve 0 1 0 1 core)
                  (assert (eq rc :ok))
                  (setf core (test-write-pool-string c15 tx-s tx-g (concatenate 'string "DUAL-S2C" crlf)))
                  (multiple-value-bind (rc rx-s rx-g c16) (fn2-core-reserve 0 1 0 1 core)
                    (assert (eq rc :ok))
                    (multiple-value-bind (sc _1 _2 c17) (fn2-issue-send srv-cap srv-nonce tx-s tx-g 0 10 0 1 0 1 0 c16)
                      (declare (ignore _1 _2))
                      (assert (eq sc :ok))
                      (multiple-value-bind (rvc _3 _4 c18) (fn2-issue-receive cli-cap cli-nonce rx-s rx-g 10 1 0 1 0 c17)
                        (declare (ignore _3 _4))
                        (assert (eq rvc :ok))
                        (multiple-value-bind (io-pair c19) (test-pump-harvest-two host c18)
                          (dolist (ev io-pair)
                            (assert (eql (fifth ev) *fn2-outcome-done*))
                            (assert (= (seventh ev) 10)))
                          (multiple-value-bind (got c20) (test-read-pool-bytes c19 rx-s rx-g 10)
                            (assert (string= (test-bytes-to-string got) (concatenate 'string "DUAL-S2C" crlf)))
                            (setf core c20)))))))
                (setf core (test-close-cap host core cli-cap cli-nonce))
                (setf core (test-close-cap host core srv-cap srv-nonce))
                (format t "PASS_DUAL_TLS_LOOPBACK~%"))))

          ;; 7. Outbound client TLS to external TLS server + CA verify + SPKI pin + record send/recv.
          (multiple-value-bind (cc _cs _cg c1) (test-issue-connect-core core *fn2-peer-family-inet* {port_tls_ok} #x7f000001 0 0 0)
            (declare (ignore _cs _cg))
            (assert (eq cc :ok))
            (setf core c1))
          (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c2)
              (test-pump-harvest host core)
            (declare (ignore os og cell reason count))
            (assert (= ev *fn2-event-connect-result*))
            (assert (eql outcome *fn2-outcome-done*))
            (setf core c2)
            (let* ((cap aux0) (nonce aux1) (cap-rec (aref (fn2-nhost-caps host) cap)))
              (fn2-n-configure-cap-client-tls host cap-rec :outbound t
                                              :server-name "peer.example"
                                              :verify-host "127.0.0.1"
                                              :expected-spki {spki_vec_lisp}
                                              :ca-file "{cert}" :verify-peer t)
              (multiple-value-bind (rc pslot pgen c3) (fn2-core-reserve 0 1 0 1 core)
                (assert (eq rc :ok))
                (setf core c3)
                (multiple-value-bind (tc _ts _tg c4) (fn2-issue-tls-start cap nonce pslot pgen 0 0 1 0 1 0 core)
                  (declare (ignore _ts _tg))
                  (assert (eq tc :ok))
                  (setf core c4))
                (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c5)
                    (test-pump-harvest host core)
                  (declare (ignore os og cell reason count aux0 aux1))
                  (assert (= ev *fn2-event-tls-result*))
                  (assert (eql outcome *fn2-outcome-done*))
                  (setf core c5)))
              (multiple-value-bind (rc spslot spgen c6) (fn2-core-reserve 0 1 0 1 core)
                (assert (eq rc :ok))
                (setf core (test-write-pool-string c6 spslot spgen (concatenate 'string "HELLO-ACL2-TLS" crlf)))
                (multiple-value-bind (sc _ss _sg c7) (fn2-issue-send cap nonce spslot spgen 0 16 0 1 0 1 0 core)
                  (declare (ignore _ss _sg))
                  (assert (eq sc :ok))
                  (setf core c7))
                (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c8)
                    (test-pump-harvest host core)
                  (declare (ignore os og cell reason aux0 aux1))
                  (assert (= ev *fn2-event-send-result*))
                  (assert (eql outcome *fn2-outcome-done*))
                  (assert (= count 16))
                  (setf core c8)))
              (multiple-value-bind (rc rpslot rpgen c9) (fn2-core-reserve 0 1 0 1 core)
                (assert (eq rc :ok))
                (setf core c9)
                (multiple-value-bind (rvc _rs _rg c10) (fn2-issue-receive cap nonce rpslot rpgen 12 1 0 1 0 core)
                  (declare (ignore _rs _rg))
                  (assert (eq rvc :ok))
                  (setf core c10))
                (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c11)
                    (test-pump-harvest host core)
                  (declare (ignore os og cell reason aux0 aux1))
                  (assert (= ev *fn2-event-receive-result*))
                  (assert (eql outcome *fn2-outcome-done*))
                  (assert (= count 12))
                  (multiple-value-bind (reply c12) (test-read-pool-bytes c11 rpslot rpgen 12)
                    (assert (string= (test-bytes-to-string reply) (concatenate 'string "200 TLS-OK" crlf)))
                    (setf core c12))))
              (setf core (test-close-cap host core cap nonce))
              (format t "PASS_TLS_CLIENT_OK~%")))

          ;; 8. Rogue cert against verified CA fails client TLS handshake cleanly.
          (multiple-value-bind (cc _cs _cg c1) (test-issue-connect-core core *fn2-peer-family-inet* {port_tls_rogue} #x7f000001 0 0 0)
            (declare (ignore _cs _cg))
            (assert (eq cc :ok))
            (setf core c1))
          (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c2)
              (test-pump-harvest host core)
            (declare (ignore os og cell reason count))
            (assert (= ev *fn2-event-connect-result*))
            (assert (eql outcome *fn2-outcome-done*))
            (setf core c2)
            (let* ((cap aux0) (nonce aux1) (cap-rec (aref (fn2-nhost-caps host) cap)))
              (fn2-n-configure-cap-client-tls host cap-rec :outbound t
                                              :server-name "peer.example"
                                              :verify-host "127.0.0.1"
                                              :expected-spki {spki_vec_lisp}
                                              :ca-file "{cert}" :verify-peer t)
              (multiple-value-bind (rc pslot pgen c3) (fn2-core-reserve 0 1 0 1 core)
                (assert (eq rc :ok))
                (setf core c3)
                (multiple-value-bind (tc _ts _tg c4) (fn2-issue-tls-start cap nonce pslot pgen 0 0 1 0 1 0 core)
                  (declare (ignore _ts _tg))
                  (assert (eq tc :ok))
                  (setf core c4))
                (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c5)
                    (test-pump-harvest host core)
                  (declare (ignore os og cell count aux0 aux1))
                  (assert (= ev *fn2-event-tls-result*))
                  (assert (eql outcome *fn2-outcome-failed*))
                  (assert (eql reason *fn2-reason-handshake*))
                  (setf core c5)))
              (setf core (test-close-cap host core cap nonce))
              (format t "PASS_TLS_CLIENT_CA_REJECT~%")))

          ;; 9. Rogue cert in pin-only mode (verify_peer=nil) fails strictly at expected-spki check,
          ;; AND sticky retired TLS selection refuses any post-failure plaintext Send!
          (multiple-value-bind (cc _cs _cg c1) (test-issue-connect-core core *fn2-peer-family-inet* {port_tls_pin_bad} #x7f000001 0 0 0)
            (declare (ignore _cs _cg))
            (assert (eq cc :ok))
            (setf core c1))
          (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c2)
              (test-pump-harvest host core)
            (declare (ignore os og cell reason count))
            (assert (= ev *fn2-event-connect-result*))
            (assert (eql outcome *fn2-outcome-done*))
            (setf core c2)
            (let* ((cap aux0) (nonce aux1) (cap-rec (aref (fn2-nhost-caps host) cap)))
              (fn2-n-configure-cap-client-tls host cap-rec :outbound t
                                              :server-name "rogue.example"
                                              :expected-spki {spki_vec_lisp}
                                              :verify-peer nil)
              (multiple-value-bind (rc pslot pgen c3) (fn2-core-reserve 0 1 0 1 core)
                (assert (eq rc :ok))
                (setf core c3)
                (multiple-value-bind (tc _ts _tg c4) (fn2-issue-tls-start cap nonce pslot pgen 0 0 1 0 1 0 core)
                  (declare (ignore _ts _tg))
                  (assert (eq tc :ok))
                  (setf core c4))
                (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c5)
                    (test-pump-harvest host core)
                  (declare (ignore os og cell count aux0 aux1))
                  (assert (= ev *fn2-event-tls-result*))
                  (assert (eql outcome *fn2-outcome-failed*))
                  (assert (eql reason *fn2-reason-handshake*))
                  (setf core c5)))
              ;; Attempt Send after pin failure: MUST fail closed without sending plaintext!
              (multiple-value-bind (rc spslot spgen c6) (fn2-core-reserve 0 1 0 1 core)
                (assert (eq rc :ok))
                (setf core (test-write-pool-string c6 spslot spgen (concatenate 'string "LEAKED-PLAIN!!" crlf)))
                (multiple-value-bind (sc _ss _sg c7) (fn2-issue-send cap nonce spslot spgen 0 16 0 1 0 1 0 core)
                  (declare (ignore _ss _sg))
                  (assert (eq sc :ok))
                  (setf core c7))
                (multiple-value-bind (os og cell ev outcome reason count aux0 aux1 c8)
                    (test-pump-harvest host core)
                  (declare (ignore os og cell reason count aux0 aux1))
                  (assert (= ev *fn2-event-send-result*))
                  (assert (eql outcome *fn2-outcome-failed*))
                  (setf core c8)))
              (setf core (test-close-cap host core cap nonce))
              (format t "PASS_TLS_CLIENT_PIN_MISMATCH~%")))

          ;; Final fd-leak check across the entire live session.
          (assert (= initial-fds (test-open-fd-count)))
          (format t "ALL_LIVE_EFFECTORS_PASS~%"))
        (fn2-n-destroy host)))
    (sb-ext:exit :code 0))
  (cl:error (c)
    (format *error-output* "~%EFFECTOR ERROR: ~A~%" c)
    (finish-output *error-output*)
    (sb-ext:exit :code 1)))
"""
            env = os.environ.copy()
            env["FN2_TLS_LIBRARY"] = str(self.tls_lib)
            env["FN_B3_LIBRARY"] = str(self.b3_lib)
            proc = subprocess.run(
                [str(self.acl2), "--timeout", "120"],
                cwd=str(ROOT),
                env=env,
                input=driver_script,
                text=True,
                capture_output=True,
                timeout=135,
            )
            for s in listen_socks:
                try:
                    s.close()
                except OSError:
                    pass
            for t in threads:
                t.join(timeout=5.0)
            self.assertEqual(
                proc.returncode, 0,
                f"ACL2 live effectors failed rc={proc.returncode}\nSTDOUT:\n{proc.stdout[-4000:]}\nSTDERR:\n{proc.stderr[-2000:]}",
            )
            for marker in [
                "PASS_ENTROPY",
                "PASS_CONNECT_V4",
                "PASS_CONNECT_REFUSED",
                "PASS_CONNECT_CANCEL",
                "PASS_DUAL_TLS_LOOPBACK",
                "PASS_TLS_CLIENT_OK",
                "PASS_TLS_CLIENT_CA_REJECT",
                "PASS_TLS_CLIENT_PIN_MISMATCH",
                "ALL_LIVE_EFFECTORS_PASS",
            ]:
                self.assertIn(marker, proc.stdout, f"missing {marker} in:\n{proc.stdout[-4000:]}")
            if has_v6:
                self.assertIn("PASS_CONNECT_V6", proc.stdout, proc.stdout[-4000:])
            self.assertEqual(bytes(pin_fail_sink), b"", f"post-pin-failure leaked data: {pin_fail_sink!r}")
            self.assertTrue(srv_results and all(srv_results), f"server checks failed: {srv_results}")


if __name__ == "__main__":
    unittest.main()

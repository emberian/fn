import socket, sys, time
port, msgid, size = int(sys.argv[1]), sys.argv[2], int(sys.argv[3])
for _ in range(120):
    try:
        s = socket.create_connection(("127.0.0.1", port), timeout=30); break
    except OSError: time.sleep(0.5)
f = s.makefile("rb")
print("greeting", f.readline().decode().strip())
s.sendall(b"POST\r\n"); r = f.readline().decode().strip(); print("POST ->", r)
if r.startswith("340"):
    head = ("From: gate <gate@example.invalid>\r\nMessage-ID: %s\r\nNewsgroups: fn.test\r\nSubject: big\r\n\r\n" % msgid).encode()
    body = b"x" * 998 + b"\r\n"
    art = head
    while len(art) + len(body) < size: art += body
    s.sendall(art + b".\r\n"); print("article octets", len(art), "->", f.readline().decode().strip())
s.sendall(b"QUIT\r\n"); print("QUIT ->", f.readline().decode().strip())

"""External Unix relay that loses an owner's reply without an image hook.

The relay forwards request bytes unchanged and holds the first answer octet.
It does not decode fn frames or infer durable acceptance. The scenario kills
and reopens the owner, then asks its persisted state to establish the outcome.
"""
import socket
import threading


class ConsumerReplyHold:
    def __init__(self, path, target):
        self.path, self.target = str(path), str(target)
        self.listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.listener.bind(self.path)
        self.listener.listen(1)
        self.listener.settimeout(0.2)
        self.reply_received = threading.Event()
        self.closed = threading.Event()
        self.connections = []
        self.error = None
        self.thread = threading.Thread(target=self.relay, daemon=True)
        self.thread.start()

    def relay(self):
        try:
            while not self.closed.is_set():
                try:
                    client, _ = self.listener.accept()
                    break
                except socket.timeout:
                    continue
            else:
                return
            server = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            self.connections.extend((client, server))
            server.connect(self.target)

            def upstream():
                try:
                    while not self.closed.is_set():
                        data = client.recv(65536)
                        if not data:
                            server.shutdown(socket.SHUT_WR)
                            return
                        server.sendall(data)
                except OSError:
                    pass

            sender = threading.Thread(target=upstream, daemon=True)
            sender.start()
            first = server.recv(1)
            if first:
                self.reply_received.set()
                self.closed.wait()
            else:
                self.error = "owner closed before any reply octet"
        except OSError as error:
            if not self.closed.is_set():
                self.error = str(error)
        finally:
            for connection in self.connections:
                try:
                    connection.shutdown(socket.SHUT_RDWR)
                except OSError:
                    pass
                connection.close()

    def close(self):
        self.closed.set()
        self.listener.close()
        for connection in self.connections:
            try:
                connection.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
        self.thread.join(timeout=2)

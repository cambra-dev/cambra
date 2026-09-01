"""Object storage behind the subset of S3 the ETL uses.

`ObjectStore` is `put`/`get`/`list_keys`; `LocalObjectStore` writes under a
directory. An S3 implementation is the same three methods over `put_object`,
`get_object`, and a `list_objects_v2` paginator, which is what makes the local
stand-in a swap rather than a simplification.
"""

from pathlib import Path
from typing import Protocol


class ObjectStore(Protocol):
    def put(self, key: str, body: bytes) -> None: ...

    def get(self, key: str) -> bytes: ...

    def list_keys(self, prefix: str) -> list[str]: ...


class LocalObjectStore:
    def __init__(self, root: str | Path) -> None:
        self._root = Path(root)
        self._root.mkdir(parents=True, exist_ok=True)

    def _path(self, key: str) -> Path:
        return self._root / key

    def put(self, key: str, body: bytes) -> None:
        path = self._path(key)
        path.parent.mkdir(parents=True, exist_ok=True)
        # Write-then-rename so a reader never sees a half-written object, which
        # is the atomicity a real object store gives for free.
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_bytes(body)
        tmp.rename(path)

    def get(self, key: str) -> bytes:
        return self._path(key).read_bytes()

    def list_keys(self, prefix: str) -> list[str]:
        base = self._root / prefix
        if not base.exists():
            return []
        return sorted(
            str(p.relative_to(self._root))
            for p in base.rglob("*")
            if p.is_file() and not p.name.endswith(".tmp")
        )

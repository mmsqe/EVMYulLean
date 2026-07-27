import sys
import hashlib
# RIPEMD160 is gated behind OpenSSL 3's "legacy" provider. Only load it when the
# hash is actually unavailable (e.g. Linux built against OpenSSL 3); if this
# Python already exposes ripemd160 (e.g. macOS), skip the ctypes dance entirely —
# hard-coding "libssl.so" fails to open on macOS, and dlopen'ing a duplicate
# libssl there aborts the process with "loading libcrypto in an unsafe way".
try:
    hashlib.new("ripemd160")
except (ValueError, TypeError):
    import ctypes, ctypes.util
    ctypes.CDLL(ctypes.util.find_library("ssl") or "libssl.so").OSSL_PROVIDER_load(None, b"legacy")

from base_types import Bytes

def left_pad_zero_bytes(value: Bytes, size: int) -> Bytes:
    """
    Left pad zeroes to `value` if it's length is less than the given `size`.

    Parameters
    ----------
    value :
        The byte string that needs to be padded.
    size :
        The number of bytes that need that need to be padded.

    Returns
    -------
    left_padded_value: `ethereum.base_types.Bytes`
        left padded byte string of given `size`.
    """
    return value.rjust(size, b"\x00")

data = bytes.fromhex(sys.argv[1])
hash_bytes = hashlib.new("ripemd160", data).digest()
padded_hash = left_pad_zero_bytes(hash_bytes, 32)
output = padded_hash
print(bytes.hex(output), end = '')

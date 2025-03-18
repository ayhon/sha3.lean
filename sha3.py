from hashlib import sha3_224, sha3_256, sha3_384, sha3_512, shake_128, shake_256

def toBitString(
    s: bytes, flip_endianness: bool = False
) -> list[1 | 0]:
    ind = lambda x : 7 - x if flip_endianness else x
    return [ 1 if byte & (1 << ind(index)) else 0
             for byte in s
             for index in range(8) ]
      
def ofBitString(
    s: bytes, flip_endianness: bool = False
) -> bytes:
    ind = lambda x : 7 - x if flip_endianness else x
    s = list(s)
    data = [
        sum(2**i * s[8*offset + ind(i)] for i in range(8))
        for offset in range(0, len(s)//8)
    ]
    return bytes(data)
    # return bytes.fromhex(hex(int("".join(str(x) for x in s), 2))[2:])

def main(args: list[str]) -> int:
    op, *args = args
    res = None
    flip_endianness = bool("FLIP" in args)
    match op:
        case "SHA3_224":
            bs = ofBitString([int(x) for x in args[0]], flip_endianness = flip_endianness)
            res = sha3_224(bs).digest()
        case "SHA3_256":
            bs = ofBitString([int(x) for x in args[0]], flip_endianness = flip_endianness)
            res = sha3_256(bs).digest()
        case "SHA3_384":
            bs = ofBitString([int(x) for x in args[0]], flip_endianness = flip_endianness)
            res = sha3_384(bs).digest()
        case "SHA3_512":
            bs = ofBitString([int(x) for x in args[0]], flip_endianness = flip_endianness)
            res = sha3_512(bs).digest()
        case "SHAKE128":
            bs = ofBitString([int(x) for x in args[0]], flip_endianness = flip_endianness)
            d = int(args[1])
            res = shake_128(bs).digest(d)
        case "SHAKE256":
            bs = ofBitString([int(x) for x in args[0]], flip_endianness = flip_endianness)
            d = int(args[1])
            res = shake_256(bs).digest(d)
        case _:
            res = None
    assert res is not None, f"Unrecognized option {op}"
    print("".join(str(x) for x in toBitString(res)))

    return 0


if __name__ == "__main__":
    import sys
    # print("".join(str(x) for x in toBitString(b"Lean")))
    sys.exit(main(sys.argv[1:]))

from hashlib import sha3_224, sha3_256, sha3_384, sha3_512, shake_128, shake_256

def main(args: list[str]) -> int:
    if not args: return 1
    op, *args = args
    res = None
    flip_endianness = bool("FLIP" in args)
    match op:
        case "SHA3_224":
            bs = args[0].encode()
            res = sha3_224(bs).digest()
        case "SHA3_256":
            bs = args[0].encode()
            res = sha3_256(bs).digest()
        case "SHA3_384":
            bs = args[0].encode()
            res = sha3_384(bs).digest()
        case "SHA3_512":
            bs = args[0].encode()
            res = sha3_512(bs).digest()
        case "SHAKE128":
            bs = args[0].encode()
            d = int(args[1])
            res = shake_128(bs).digest(d)
        case "SHAKE256":
            bs = args[0].encode()
            d = int(args[1])
            res = shake_256(bs).digest(d)
        case _:
            res = None
    assert res is not None, f"Unrecognized option {op}"
    print(res.hex())

    return 0


if __name__ == "__main__":
    import sys
    # print("".join(str(x) for x in toBitString(b"Lean")))
    sys.exit(main(sys.argv[1:]))

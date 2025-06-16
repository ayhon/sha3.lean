/- 
See https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/example-values 
-/
import Sha3.Spec

open Spec
local instance: OfNat Bool 0 where ofNat := false
local instance: OfNat Bool 1 where ofNat := true

-- SHA3
-- Message 0 bytes
#eval Utils.dump <| SHA3_224 #[]
#eval Utils.dump <| SHA3_256 #[]
#eval Utils.dump <| SHA3_384 #[]
#eval Utils.dump <| SHA3_512 #[]
-- Message 30 bytes
#eval Utils.dump <| SHA3_224 <| Array.mk <| [1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0]
#eval Utils.dump <| SHA3_256 <| Array.mk <| [1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0]
#eval Utils.dump <| SHA3_384 <| Array.mk <| [1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0]
#eval Utils.dump <| SHA3_512 <| Array.mk <| [1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0]
-- Message 1600 bytes
#eval Utils.dump <| SHA3_224 <| Array.mk <| (List.replicate 200 [1,1,0,0, 0,1,0,1] |>.flatten)
#eval Utils.dump <| SHA3_256 <| Array.mk <| (List.replicate 200 [1,1,0,0, 0,1,0,1] |>.flatten)
#eval Utils.dump <| SHA3_384 <| Array.mk <| (List.replicate 200 [1,1,0,0, 0,1,0,1] |>.flatten)
#eval Utils.dump <| SHA3_512 <| Array.mk <| (List.replicate 200 [1,1,0,0, 0,1,0,1] |>.flatten)
-- Message 1605 bytes
#eval Utils.dump <| SHA3_224 <| Array.mk <| (List.replicate 200 [1,1,0,0, 0,1,0,1] |>.flatten) ++ [1,1,0,0, 0]
#eval Utils.dump <| SHA3_256 <| Array.mk <| (List.replicate 200 [1,1,0,0, 0,1,0,1] |>.flatten) ++ [1,1,0,0, 0]
#eval Utils.dump <| SHA3_384 <| Array.mk <| (List.replicate 200 [1,1,0,0, 0,1,0,1] |>.flatten) ++ [1,1,0,0, 0]
#eval Utils.dump <| SHA3_512 <| Array.mk <| (List.replicate 200 [1,1,0,0, 0,1,0,1] |>.flatten) ++ [1,1,0,0, 0]
-- Message 1630 bytes
#eval Utils.dump <| SHA3_224 <| Array.mk <| (List.replicate 203 [1,1,0,0, 0,1,0,1] |>.flatten) ++ [1,1,0,0, 0,1]
#eval Utils.dump <| SHA3_256 <| Array.mk <| (List.replicate 200 [1,1,0,0, 0,1,0,1] |>.flatten) ++ [1,1,0,0, 0,1]
#eval Utils.dump <| SHA3_384 <| Array.mk <| (List.replicate 200 [1,1,0,0, 0,1,0,1] |>.flatten) ++ [1,1,0,0, 0,1]
#eval Utils.dump <| SHA3_512 <| Array.mk <| (List.replicate 200 [1,1,0,0, 0,1,0,1] |>.flatten) ++ [1,1,0,0, 0,1]


-- Shake truncation
-- Output length = 4096
#eval Utils.dump <| SHAKE128 (d := 4096) #[]
-- Output length = 4095
#eval Utils.dump <| SHAKE128 (d := 4095) #[]
-- Output length = 4094
#eval Utils.dump <| SHAKE128 (d := 4094) #[]
-- Output length = 4093
#eval Utils.dump <| SHAKE128 (d := 4093) #[]
-- Output length = 4092
#eval Utils.dump <| SHAKE128 (d := 4092) #[]
-- Output length = 4091
#eval Utils.dump <| SHAKE128 (d := 4091) #[]
-- Output length = 4090
#eval Utils.dump <| SHAKE128 (d := 4090) #[]

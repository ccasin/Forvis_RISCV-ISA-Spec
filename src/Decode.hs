module Decode (Instruction (..), decode)  where

-- ================================================================
-- This module defines the type 'Instruction' for decoded instructions
-- and a 'decode' function from 32-bit words to decoded instructions.

-- ================================================================
-- Haskell lib imports

import Data.Bits    -- For bit-wise 'and' (.&.) etc.
import Data.Word    -- For Wordxx type (unsigned fixed-width ints)
import Data.Int     -- For Intxx type (signed fixed-width ints)

-- Local imports

import BitManipulation
import ArchDefs
import CSRFile (misa_mxl, misa_flag)

-- ================================================================
-- Decoded instructions

data Instruction =
  IllegalInstruction |

  Lb  { rd :: Register, rs1 :: Register, oimm12 :: UInt } |
  Lh  { rd :: Register, rs1 :: Register, oimm12 :: UInt } |
  Lw  { rd :: Register, rs1 :: Register, oimm12 :: UInt } |
  Ld  { rd :: Register, rs1 :: Register, oimm12 :: UInt } |
  Lbu { rd :: Register, rs1 :: Register, oimm12 :: UInt } |
  Lhu { rd :: Register, rs1 :: Register, oimm12 :: UInt } |
  Lwu { rd :: Register, rs1 :: Register, oimm12 :: UInt } |

  Fence { pred :: UInt, succ :: UInt } |
  Fence_i |

  Addi  { rd :: Register, rs1 :: Register, imm12  :: UInt } |
  Slli  { rd :: Register, rs1 :: Register, shamt6 :: UInt } |
  Slti  { rd :: Register, rs1 :: Register, imm12  :: UInt } |
  Sltiu { rd :: Register, rs1 :: Register, imm12  :: UInt } |
  Xori  { rd :: Register, rs1 :: Register, imm12  :: UInt } |
  Ori   { rd :: Register, rs1 :: Register, imm12  :: UInt } |
  Andi  { rd :: Register, rs1 :: Register, imm12  :: UInt } |
  Srli  { rd :: Register, rs1 :: Register, shamt6 :: UInt } |
  Srai  { rd :: Register, rs1 :: Register, shamt6 :: UInt } |

  Auipc { rd :: Register, oimm20 :: UInt } |

  Addiw { rd :: Register, rs1 :: Register, imm12  :: UInt } |
  Slliw { rd :: Register, rs1 :: Register, shamt5 :: UInt } |
  Srliw { rd :: Register, rs1 :: Register, shamt5 :: UInt } |
  Sraiw { rd :: Register, rs1 :: Register, shamt5 :: UInt } |

  Sb { rs1 :: Register, rs2 :: Register, simm12 :: UInt } |
  Sh { rs1 :: Register, rs2 :: Register, simm12 :: UInt } |
  Sw { rs1 :: Register, rs2 :: Register, simm12 :: UInt } |
  Sd { rs1 :: Register, rs2 :: Register, simm12 :: UInt } |

  Add    { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sub    { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sll    { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Slt    { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sltu   { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Xor    { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Srl    { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sra    { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Or     { rd :: Register, rs1 :: Register, rs2 :: Register } |
  And    { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Mul    { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Mulh   { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Mulhsu { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Mulhu  { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Div    { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Divu   { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Rem    { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Remu   { rd :: Register, rs1 :: Register, rs2 :: Register } |

  Lui { rd :: Register, imm20 :: UInt } |

  Addw  { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Subw  { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sllw  { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Srlw  { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sraw  { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Mulw  { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Divw  { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Divuw { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Remw  { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Remuw { rd :: Register, rs1 :: Register, rs2 :: Register } |

  Beq  { rs1 :: Register, rs2 :: Register, sbimm12 :: UInt } |
  Bne  { rs1 :: Register, rs2 :: Register, sbimm12 :: UInt } |
  Blt  { rs1 :: Register, rs2 :: Register, sbimm12 :: UInt } |
  Bge  { rs1 :: Register, rs2 :: Register, sbimm12 :: UInt } |
  Bltu { rs1 :: Register, rs2 :: Register, sbimm12 :: UInt } |
  Bgeu { rs1 :: Register, rs2 :: Register, sbimm12 :: UInt } |

  Jalr { rd :: Register, rs1 :: Register, oimm12 :: UInt } |
  Jal  { rd :: Register, jimm20 :: UInt } |

  Ecall  |
  Ebreak |
  Uret   |
  Sret   |
  Mret   |
  Wfi    |
  Sfence_vm { rs1 :: Register, rs2 :: Register } |

  Csrrw  { rd :: Register,  rs1 :: Register, csr12 :: CSR_Addr } |
  Csrrs  { rd :: Register,  rs1 :: Register, csr12 :: CSR_Addr } |
  Csrrc  { rd :: Register,  rs1 :: Register, csr12 :: CSR_Addr } |
  Csrrwi { rd :: Register, zimm :: UInt,     csr12 :: CSR_Addr } |
  Csrrsi { rd :: Register, zimm :: UInt,     csr12 :: CSR_Addr } |
  Csrrci { rd :: Register, zimm :: UInt,     csr12 :: CSR_Addr }
  deriving (Eq, Show)

-- ================================================================
-- Instruction bit fields
-- These are all private to this module.
-- cf. "The RISC-V Instruction Set Manual, Volume I:  User-level ISA, version 2.2"
-- cf. "The RISC-V Instruction Set Manual, Volume II: Privileged Architecture, version 1.10"
-- both available from:    https://riscv.org/specifications/

-- Major opcode (instr [6:0]), see Table 19.1 in spec
type Opcode = Word32

opcode_LOAD      :: Opcode;    opcode_LOAD      = 0x03    -- 7'b_00_000_11
opcode_LOAD_FP   :: Opcode;    opcode_LOAD_FP   = 0x07    -- 7'b_00_001_11
opcode_MISC_MEM  :: Opcode;    opcode_MISC_MEM  = 0x0F    -- 7'b_00_011_11
opcode_OP_IMM    :: Opcode;    opcode_OP_IMM    = 0x13    -- 7'b_00_100_11
opcode_AUIPC     :: Opcode;    opcode_AUIPC     = 0x17    -- 7'b_00_101_11
opcode_OP_IMM_32 :: Opcode;    opcode_OP_IMM_32 = 0x1B    -- 7'b_00_110_11

opcode_STORE     :: Opcode;    opcode_STORE     = 0x23    -- 7'b_01_000_11
opcode_STORE_FP  :: Opcode;    opcode_STORE_FP  = 0x27    -- 7'b_01_001_11
opcode_AMO       :: Opcode;    opcode_AMO       = 0x2F    -- 7'b_01_011_11
opcode_OP        :: Opcode;    opcode_OP        = 0x33    -- 7'b_01_100_11
opcode_LUI       :: Opcode;    opcode_LUI       = 0x37    -- 7'b_01_101_11
opcode_OP_32     :: Opcode;    opcode_OP_32     = 0x3B    -- 7'b_01_110_11

opcode_MADD      :: Opcode;    opcode_MADD      = 0x43    -- 7'b_10_000_11
opcode_MSUB      :: Opcode;    opcode_MSUB      = 0x47    -- 7'b_10_001_11
opcode_NMSUB     :: Opcode;    opcode_NMSUB     = 0x4B    -- 7'b_10_010_11
opcode_NMADD     :: Opcode;    opcode_NMADD     = 0x4F    -- 7'b_10_011_11
opcode_OP_FP     :: Opcode;    opcode_OP_FP     = 0x53    -- 7'b_10_100_11

opcode_BRANCH    :: Opcode;    opcode_BRANCH    = 0x63    -- 7'b_11_000_11
opcode_JALR      :: Opcode;    opcode_JALR      = 0x67    -- 7'b_11_001_11
opcode_JAL       :: Opcode;    opcode_JAL       = 0x6F    -- 7'b_11_011_11
opcode_SYSTEM    :: Opcode;    opcode_SYSTEM    = 0x73    -- 7'b_11_100_11

-- LOAD sub-opcodes
funct3_LB  :: Word32;    funct3_LB  = 0x0     -- 3'b_000
funct3_LH  :: Word32;    funct3_LH  = 0x1     -- 3'b_001
funct3_LW  :: Word32;    funct3_LW  = 0x2     -- 3'b_010
funct3_LD  :: Word32;    funct3_LD  = 0x3     -- 3'b_011
funct3_LBU :: Word32;    funct3_LBU = 0x4     -- 3'b_100
funct3_LHU :: Word32;    funct3_LHU = 0x5     -- 3'b_101
funct3_LWU :: Word32;    funct3_LWU = 0x6     -- 3'b_110

-- MISC_MEM sub-opcodes
funct3_FENCE   :: Word32;    funct3_FENCE   = 0x0      -- 3'b_000
funct3_FENCE_I :: Word32;    funct3_FENCE_I = 0x1      -- 3'b_001

-- OP_IMM sub-opcodes
funct3_ADDI  :: Word32;    funct3_ADDI  = 0x0      -- 3'b_000
funct3_SLLI  :: Word32;    funct3_SLLI  = 0x1      -- 3'b_001
funct3_SLTI  :: Word32;    funct3_SLTI  = 0x2      -- 3'b_010
funct3_SLTIU :: Word32;    funct3_SLTIU = 0x3      -- 3'b_011
funct3_XORI  :: Word32;    funct3_XORI  = 0x4      -- 3'b_100
funct3_SRLI  :: Word32;    funct3_SRLI  = 0x5      -- 3'b_101
funct3_SRAI  :: Word32;    funct3_SRAI  = 0x5      -- 3'b_101
funct3_ORI   :: Word32;    funct3_ORI   = 0x6      -- 3'b_110
funct3_ANDI  :: Word32;    funct3_ANDI  = 0x7      -- 3'b_111

-- OP_IMM.SLLI/SRLI/SRAI for RV32
funct7_SLLI  :: Word32;    funct7_SLLI  = 0x00     -- 7'b_0000000
funct7_SRLI  :: Word32;    funct7_SRLI  = 0x00     -- 7'b_0000000
funct7_SRAI  :: Word32;    funct7_SRAI  = 0x20     -- 7'b_0100000
-- OP_IMM.SLLI/SRLI/SRAI for RV64
funct6_SLLI  :: Word32;    funct6_SLLI  = 0x00     -- 6'b_000000
funct6_SRLI  :: Word32;    funct6_SRLI  = 0x00     -- 6'b_000000
funct6_SRAI  :: Word32;    funct6_SRAI  = 0x10     -- 6'b_010000

-- OP_IMM_32 sub-opcodes (RV64 only)
funct3_ADDIW :: Word32;    funct3_ADDIW = 0x0     -- 3'b_000

funct3_SLLIW :: Word32;    funct3_SLLIW = 0x1     -- 3'b_001
funct7_SLLIW :: Word32;    funct7_SLLIW = 0x00    -- 7'b_0000000

funct3_SRLIW :: Word32;    funct3_SRLIW = 0x5     -- 3'b_101
funct7_SRLIW :: Word32;    funct7_SRLIW = 0x00    -- 7'b_0000000

funct3_SRAIW :: Word32;    funct3_SRAIW = 0x5     -- 3'b_101
funct7_SRAIW :: Word32;    funct7_SRAIW = 0x20    -- 7'b_0100000

-- STORE sub-opcodes
funct3_SB :: Word32;    funct3_SB = 0x0     -- 3'b_000
funct3_SH :: Word32;    funct3_SH = 0x1     -- 3'b_001
funct3_SW :: Word32;    funct3_SW = 0x2     -- 3'b_010
funct3_SD :: Word32;    funct3_SD = 0x3     -- 3'b_011

-- OP sub-opcodes
funct3_ADD  :: Word32;    funct3_ADD  = 0x0     -- 3'b_000
funct7_ADD  :: Word32;    funct7_ADD  = 0x00    -- 7'b_000_0000

funct3_SUB  :: Word32;    funct3_SUB  = 0x0     -- 3'b_000
funct7_SUB  :: Word32;    funct7_SUB  = 0x20    -- 7'b_010_0000

funct3_SLL  :: Word32;    funct3_SLL  = 0x1     -- 3'b_001
funct7_SLL  :: Word32;    funct7_SLL  = 0x00    -- 7'b_000_0000

funct3_SLT  :: Word32;    funct3_SLT  = 0x2     -- 3'b_010
funct7_SLT  :: Word32;    funct7_SLT  = 0x00    -- 7'b_000_0000

funct3_SLTU :: Word32;    funct3_SLTU = 0x3     -- 3'b_011
funct7_SLTU :: Word32;    funct7_SLTU = 0x00    -- 7'b_000_0000

funct3_XOR  :: Word32;    funct3_XOR  = 0x4     -- 3'b_100
funct7_XOR  :: Word32;    funct7_XOR  = 0x00    -- 7'b_000_0000

funct3_SRL  :: Word32;    funct3_SRL  = 0x5     -- 3'b_101
funct7_SRL  :: Word32;    funct7_SRL  = 0x00    -- 7'b_000_0000

funct3_SRA  :: Word32;    funct3_SRA  = 0x5     -- 3'b_101
funct7_SRA  :: Word32;    funct7_SRA  = 0x20    -- 7'b_010_0000

funct3_OR   :: Word32;    funct3_OR   = 0x6     -- 3'b_110
funct7_OR   :: Word32;    funct7_OR   = 0x00    -- 7'b_000_0000

funct3_AND  :: Word32;    funct3_AND  = 0x7     -- 3'b_111
funct7_AND  :: Word32;    funct7_AND  = 0x00    -- 7'b_000_0000

-- OP sub-opcodes, M standard extension

funct3_MUL    :: Word32;    funct3_MUL    = 0x0     -- 3'b_000
funct7_MUL    :: Word32;    funct7_MUL    = 0x01    -- 7'b_000_0001

funct3_MULH   :: Word32;    funct3_MULH   = 0x1     -- 3'b_001
funct7_MULH   :: Word32;    funct7_MULH   = 0x01    -- 7'b_000_0001

funct3_MULHSU :: Word32;    funct3_MULHSU = 0x2     -- 3'b_010
funct7_MULHSU :: Word32;    funct7_MULHSU = 0x01    -- 7'b_000_0001

funct3_MULHU  :: Word32;    funct3_MULHU  = 0x3     -- 3'b_011
funct7_MULHU  :: Word32;    funct7_MULHU  = 0x01    -- 7'b_000_0001

funct3_DIV    :: Word32;    funct3_DIV    = 0x4     -- 3'b_100
funct7_DIV    :: Word32;    funct7_DIV    = 0x01    -- 7'b_000_0001

funct3_DIVU   :: Word32;    funct3_DIVU   = 0x5     -- 3'b_101
funct7_DIVU   :: Word32;    funct7_DIVU   = 0x01    -- 7'b_000_0001

funct3_REM    :: Word32;    funct3_REM    = 0x6     -- 3'b_110
funct7_REM    :: Word32;    funct7_REM    = 0x01    -- 7'b_000_0001

funct3_REMU   :: Word32;    funct3_REMU   = 0x7     -- 3'b_111
funct7_REMU   :: Word32;    funct7_REMU   = 0x01    -- 7'b_000_0001

-- OP_32 sub-opcodes (RV64 only)
funct3_ADDW  :: Word32;    funct3_ADDW  = 0x0     --- 3'b_000
funct7_ADDW  :: Word32;    funct7_ADDW  = 0x00    --- 7'b_000_0000

funct3_SUBW  :: Word32;    funct3_SUBW  = 0x0     --- 3'b_000
funct7_SUBW  :: Word32;    funct7_SUBW  = 0x20    --- 7'b_010_0000

funct3_SLLW  :: Word32;    funct3_SLLW  = 0x1     --- 3'b_001
funct7_SLLW  :: Word32;    funct7_SLLW  = 0x00    --- 7'b_000_0000

funct3_SRLW  :: Word32;    funct3_SRLW  = 0x5     --- 3'b_101
funct7_SRLW  :: Word32;    funct7_SRLW  = 0x00    --- 7'b_000_0000

funct3_SRAW  :: Word32;    funct3_SRAW  = 0x5     --- 3'b_101
funct7_SRAW  :: Word32;    funct7_SRAW  = 0x20    --- 7'b_010_0000

-- OP_32 sub-opcodes, M standard extension (RV64 only)
funct3_MULW  :: Word32;    funct3_MULW  = 0x0     --- 3'b_000
funct7_MULW  :: Word32;    funct7_MULW  = 0x01    --- 7'b_000_0001

funct3_DIVW  :: Word32;    funct3_DIVW  = 0x4     --- 3'b_100
funct7_DIVW  :: Word32;    funct7_DIVW  = 0x01    --- 7'b_000_0001

funct3_DIVUW :: Word32;    funct3_DIVUW = 0x5     --- 3'b_101
funct7_DIVUW :: Word32;    funct7_DIVUW = 0x01    --- 7'b_000_0001

funct3_REMW  :: Word32;    funct3_REMW  = 0x6     --- 3'b_110
funct7_REMW  :: Word32;    funct7_REMW  = 0x01    --- 7'b_000_0001

funct3_REMUW :: Word32;    funct3_REMUW = 0x7     --- 3'b_111
funct7_REMUW :: Word32;    funct7_REMUW = 0x01    --- 7'b_000_0001

-- BRANCH sub-opcodes
funct3_BEQ  :: Word32;    funct3_BEQ  = 0x0     -- 3'b_000
funct3_BNE  :: Word32;    funct3_BNE  = 0x1     -- 3'b_001
funct3_BLT  :: Word32;    funct3_BLT  = 0x4     -- 3'b_100
funct3_BGE  :: Word32;    funct3_BGE  = 0x5     -- 3'b_101
funct3_BLTU :: Word32;    funct3_BLTU = 0x6     -- 3'b_110
funct3_BGEU :: Word32;    funct3_BGEU = 0x7     -- 3'b_111

-- SYSTEM sub-opcodes
funct3_PRIV   :: Word32;    funct3_PRIV   = 0x0     -- 3'b_000
--- SYSTEM.PRIV sub-sub-opcodes
funct12_ECALL    :: Word32;    funct12_ECALL  = 0x000    -- 12'b_0000_0000_0000
funct12_EBREAK   :: Word32;    funct12_EBREAK = 0x001    -- 12'b_0000_0000_0001
funct12_URET     :: Word32;    funct12_URET   = 0x002    -- 12'b_0000_0000_0010
funct12_SRET     :: Word32;    funct12_SRET   = 0x102    -- 12'b_0001_0000_0010
funct12_MRET     :: Word32;    funct12_MRET   = 0x302    -- 12'b_0011_0000_0010
funct12_WFI      :: Word32;    funct12_WFI    = 0x105    -- 12'b_0001_0000_0101

funct7_SFENCE_VM :: Word32;    funct7_SFENCE_VM = 0x09     -- 7'b_000_1001

funct3_CSRRW  :: Word32;    funct3_CSRRW  = 0x1     -- 3'b_001
funct3_CSRRS  :: Word32;    funct3_CSRRS  = 0x2     -- 3'b_010
funct3_CSRRC  :: Word32;    funct3_CSRRC  = 0x3     -- 3'b_011
funct3_CSRRWI :: Word32;    funct3_CSRRWI = 0x5     -- 3'b_101
funct3_CSRRSI :: Word32;    funct3_CSRRSI = 0x6     -- 3'b_110
funct3_CSRRCI :: Word32;    funct3_CSRRCI = 0x7     -- 3'b_111

-- TODO: sub-opcodes for LOAD_FP, STORE_FP, OP_FP
-- TODO: sub-opcodes for AMO
-- TODO: sub-opcodes for MADD, MSUB, NMSUB, NMADD

-- ================================================================
-- The main decoder function
-- TODO: more filters needed using MISA bits

decode :: RV -> UInt -> Word32 -> Instruction
decode  rv  misa  instr = decode_sub  opcode
  where
    -- Symbolic names for notable bitfields in the 32b instruction 'instr'
    -- Note: 'bitSlice x i j' is, roughly, Verilog's 'x [j-1, i]'
    opcode  = bitSlice instr 0 7        -- = Verilog's: instr [6:0]
    funct3  = bitSlice instr 12 15
    funct7  = bitSlice instr 25 32
    funct10 = (shift (bitSlice instr 25 32) 3) .|. (bitSlice instr 12 15)
    funct12 = bitSlice instr 20 32

    rd      = toEnum (fromIntegral (bitSlice instr 7 12))
    rs1     = toEnum (fromIntegral (bitSlice instr 15 20))
    rs2     = toEnum (fromIntegral (bitSlice instr 20 25))
    -- rs3     = toEnum (fromIntegral (bitSlice instr 27 32))    -- TODO: for FMADD, FMSUB, FNMSUB?

    succ    = zeroExtend_u32_to_u64  (bitSlice instr 20 24)                     -- for FENCE
    pred    = zeroExtend_u32_to_u64  (bitSlice instr 24 28)                     -- for FENCE
    msb4    = bitSlice instr 28 32                                              -- for FENCE

    imm20   = zeroExtend_u32_to_u64  (bitSlice instr 12 32)                     -- for LUI
    oimm20  = zeroExtend_u32_to_u64  (bitSlice instr 12 32)                     -- for AUIPC

    jimm20  = zeroExtend_u32_to_u64  (shift (bitSlice instr 31 32) 19  .|.    -- for JAL
                                      shift (bitSlice instr 21 31)  0  .|.
                                      shift (bitSlice instr 20 21) 10  .|.
                                      shift (bitSlice instr 12 20) 11)

    imm12   = zeroExtend_u32_to_u64  (bitSlice instr 20 32)
    oimm12  = zeroExtend_u32_to_u64  (bitSlice instr 20 32)

    csr12   = zeroExtend_u32_to_u64  (bitSlice instr 20 32)

    simm12  = zeroExtend_u32_to_u64  (shift (bitSlice instr 25 32) 5 .|. bitSlice instr 7 12)    -- for STORE

    sbimm12 = zeroExtend_u32_to_u64  (shift (bitSlice instr 31 32) 11  .|.    -- for BRANCH
                                      shift (bitSlice instr 25 31)  4  .|.
                                      shift (bitSlice instr  8 12)  0  .|.
                                      shift (bitSlice instr  7  8) 10)

    shamt5  = zeroExtend_u32_to_u64  (bitSlice instr 20 25)    -- for RV32 SLLI, SRLI, SRAI
    shamt6  = zeroExtend_u32_to_u64  (bitSlice instr 20 26)    -- for RV64 SLLI, SRLI, SRAI
    funct6  = bitSlice instr 26 32    -- for RV64 SLLI, SRLI, SRAI

    zimm    = zeroExtend_u32_to_u64  (bitSlice instr 15 20)    -- for CSRRxI

    decode_sub opcode
      | opcode==opcode_LOAD, funct3==funct3_LB  = Lb  {rd=rd, rs1=rs1, oimm12=oimm12}
      | opcode==opcode_LOAD, funct3==funct3_LH  = Lh  {rd=rd, rs1=rs1, oimm12=oimm12}
      | opcode==opcode_LOAD, funct3==funct3_LW  = Lw  {rd=rd, rs1=rs1, oimm12=oimm12}
      | opcode==opcode_LOAD, funct3==funct3_LBU = Lbu {rd=rd, rs1=rs1, oimm12=oimm12}
      | opcode==opcode_LOAD, funct3==funct3_LHU = Lhu {rd=rd, rs1=rs1, oimm12=oimm12}

      | opcode==opcode_MISC_MEM, rd==Rg_x0, funct3==funct3_FENCE,   rs1==Rg_x0, msb4==0  = Fence {Decode.pred=pred, Decode.succ=succ}
      | opcode==opcode_MISC_MEM, rd==Rg_x0, funct3==funct3_FENCE_I, rs1==Rg_x0, imm12==0 = Fence_i

      | opcode==opcode_OP_IMM, funct3==funct3_ADDI                                = Addi  {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM, funct3==funct3_SLLI, funct7==funct7_SLLI, rv==RV32 = Slli  {rd=rd, rs1=rs1, shamt6=shamt5}
      | opcode==opcode_OP_IMM, funct3==funct3_SLTI                                = Slti  {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM, funct3==funct3_SLTIU                               = Sltiu {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM, funct3==funct3_XORI                                = Xori  {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM, funct3==funct3_ORI                                 = Ori   {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM, funct3==funct3_ANDI                                = Andi  {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM, funct3==funct3_SRLI, funct7==funct7_SRLI, rv==RV32 = Srli  {rd=rd, rs1=rs1, shamt6=shamt5}
      | opcode==opcode_OP_IMM, funct3==funct3_SRAI, funct7==funct7_SRAI, rv==RV32 = Srai  {rd=rd, rs1=rs1, shamt6=shamt5}

      | opcode==opcode_AUIPC = Auipc {rd=rd, oimm20=oimm20}

      | opcode==opcode_STORE, funct3==funct3_SB = Sb {rs1=rs1, rs2=rs2, simm12=simm12}
      | opcode==opcode_STORE, funct3==funct3_SH = Sh {rs1=rs1, rs2=rs2, simm12=simm12}
      | opcode==opcode_STORE, funct3==funct3_SW = Sw {rs1=rs1, rs2=rs2, simm12=simm12}

      | opcode==opcode_OP, funct3==funct3_ADD,  funct7==funct7_ADD  = Add  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SUB,  funct7==funct7_SUB  = Sub  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SLL,  funct7==funct7_SLL  = Sll  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SLT,  funct7==funct7_SLT  = Slt  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SLTU, funct7==funct7_SLTU = Sltu {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_XOR,  funct7==funct7_XOR  = Xor  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SRL,  funct7==funct7_SRL  = Srl  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SRA,  funct7==funct7_SRA  = Sra  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_OR,   funct7==funct7_OR   = Or   {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_AND,  funct7==funct7_AND  = And  {rd=rd, rs1=rs1, rs2=rs2}

      | opcode==opcode_OP, funct3==funct3_MUL,    funct7==funct7_MUL    = Mul    {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_MULH,   funct7==funct7_MULH   = Mulh   {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_MULHSU, funct7==funct7_MULHSU = Mulhsu {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_MULHU,  funct7==funct7_MULHU  = Mulhu  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_DIV,    funct7==funct7_DIV    = Div    {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_DIVU,   funct7==funct7_DIVU   = Divu   {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_REM,    funct7==funct7_REM    = Rem    {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_REMU,   funct7==funct7_REMU   = Remu   {rd=rd, rs1=rs1, rs2=rs2}

      | opcode==opcode_LUI = Lui {rd=rd, imm20=imm20}

      | opcode==opcode_BRANCH, funct3==funct3_BEQ  = Beq  {rs1=rs1, rs2=rs2, sbimm12=sbimm12}
      | opcode==opcode_BRANCH, funct3==funct3_BNE  = Bne  {rs1=rs1, rs2=rs2, sbimm12=sbimm12}
      | opcode==opcode_BRANCH, funct3==funct3_BLT  = Blt  {rs1=rs1, rs2=rs2, sbimm12=sbimm12}
      | opcode==opcode_BRANCH, funct3==funct3_BGE  = Bge  {rs1=rs1, rs2=rs2, sbimm12=sbimm12}
      | opcode==opcode_BRANCH, funct3==funct3_BLTU = Bltu {rs1=rs1, rs2=rs2, sbimm12=sbimm12}
      | opcode==opcode_BRANCH, funct3==funct3_BGEU = Bgeu {rs1=rs1, rs2=rs2, sbimm12=sbimm12}

      | opcode==opcode_JALR = Jalr {rd=rd, rs1=rs1, oimm12=oimm12}

      | opcode==opcode_JAL  = Jal {rd=rd, jimm20=jimm20}

      | opcode==opcode_SYSTEM, rd==Rg_x0, funct3==funct3_PRIV, rs1==Rg_x0, funct12==funct12_ECALL  = Ecall
      | opcode==opcode_SYSTEM, rd==Rg_x0, funct3==funct3_PRIV, rs1==Rg_x0, funct12==funct12_EBREAK = Ebreak
      | opcode==opcode_SYSTEM, rd==Rg_x0, funct3==funct3_PRIV, rs1==Rg_x0, funct12==funct12_URET   = Uret
      | opcode==opcode_SYSTEM, rd==Rg_x0, funct3==funct3_PRIV, rs1==Rg_x0, funct12==funct12_SRET   = Sret
      | opcode==opcode_SYSTEM, rd==Rg_x0, funct3==funct3_PRIV, rs1==Rg_x0, funct12==funct12_MRET   = Mret
      | opcode==opcode_SYSTEM, rd==Rg_x0, funct3==funct3_PRIV, rs1==Rg_x0, funct12==funct12_WFI    = Wfi

      | opcode==opcode_SYSTEM, rd==Rg_x0, funct3==funct3_PRIV, funct7==funct7_SFENCE_VM        = Sfence_vm {rs1=rs1, rs2=rs2}

      | opcode==opcode_SYSTEM, funct3==funct3_CSRRW  = Csrrw   {rd=rd, rs1=rs1,   csr12=csr12}
      | opcode==opcode_SYSTEM, funct3==funct3_CSRRS  = Csrrs   {rd=rd, rs1=rs1,   csr12=csr12}
      | opcode==opcode_SYSTEM, funct3==funct3_CSRRC  = Csrrc   {rd=rd, rs1=rs1,   csr12=csr12}
      | opcode==opcode_SYSTEM, funct3==funct3_CSRRWI = Csrrwi  {rd=rd, zimm=zimm, csr12=csr12}
      | opcode==opcode_SYSTEM, funct3==funct3_CSRRSI = Csrrsi  {rd=rd, zimm=zimm, csr12=csr12}
      | opcode==opcode_SYSTEM, funct3==funct3_CSRRCI = Csrrci  {rd=rd, zimm=zimm, csr12=csr12}

      -- The following are RV64 only
      | opcode==opcode_LOAD, funct3==funct3_LD,  rv==RV64 = Ld  {rd=rd, rs1=rs1, oimm12=oimm12}
      | opcode==opcode_LOAD, funct3==funct3_LWU, rv==RV64 = Lwu {rd=rd, rs1=rs1, oimm12=oimm12}

      | opcode==opcode_OP_IMM, funct3==funct3_SLLI, funct6==funct6_SLLI, rv==RV64 = Slli  {rd=rd, rs1=rs1, shamt6=shamt6}
      | opcode==opcode_OP_IMM, funct3==funct3_SRLI, funct6==funct6_SRLI, rv==RV64 = Srli  {rd=rd, rs1=rs1, shamt6=shamt6}
      | opcode==opcode_OP_IMM, funct3==funct3_SRAI, funct6==funct6_SRAI, rv==RV64 = Srai  {rd=rd, rs1=rs1, shamt6=shamt6}

      | opcode==opcode_OP_IMM_32, funct3==funct3_ADDIW,                       rv==RV64 = Addiw  {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM_32, funct3==funct3_SLLIW, funct7==funct7_SLLIW, rv==RV64 = Slliw  {rd=rd, rs1=rs1, shamt5=shamt5}
      | opcode==opcode_OP_IMM_32, funct3==funct3_SRLIW, funct7==funct7_SRLIW, rv==RV64 = Srliw  {rd=rd, rs1=rs1, shamt5=shamt5}
      | opcode==opcode_OP_IMM_32, funct3==funct3_SRAIW, funct7==funct7_SRAIW, rv==RV64 = Sraiw  {rd=rd, rs1=rs1, shamt5=shamt5}

      | opcode==opcode_STORE, funct3==funct3_SD, rv==RV64 = Sd {rs1=rs1, rs2=rs2, simm12=simm12}

      | opcode==opcode_OP_32, funct3==funct3_ADDW,  funct7==funct7_ADDW,  rv==RV64 = Addw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_SUBW,  funct7==funct7_SUBW,  rv==RV64 = Subw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_SLLW,  funct7==funct7_SLLW,  rv==RV64 = Sllw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_SRLW,  funct7==funct7_SRLW,  rv==RV64 = Srlw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_SRAW,  funct7==funct7_SRAW,  rv==RV64 = Sraw  {rd=rd, rs1=rs1, rs2=rs2}

      | opcode==opcode_OP_32, funct3==funct3_MULW,  funct7==funct7_MULW,  rv==RV64 = Mulw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_DIVW,  funct7==funct7_DIVW,  rv==RV64 = Divw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_DIVUW, funct7==funct7_DIVUW, rv==RV64 = Divuw {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_REMW,  funct7==funct7_REMW,  rv==RV64 = Remw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_REMUW, funct7==funct7_REMUW, rv==RV64 = Remuw {rd=rd, rs1=rs1, rs2=rs2}

      | True                      = IllegalInstruction

-- ================================================================

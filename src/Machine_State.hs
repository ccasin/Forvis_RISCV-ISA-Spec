-- Copyright (c) 2018-2019 Rishiyur S. Nikhil
-- See LICENSE for license details

module Machine_State where

-- ================================================================
-- This module defines the data structure holding the RISC-V CPU archtectural state
-- (plus some additional state for debugging/tracing convience)
-- and a read/write API to read and write components of the state.
-- Also defines 'ifetch' (instruction fetch).

-- ================================================================
-- Standard Haskell imports

import Data.Maybe
import Data.Int
import Data.Bits
import qualified Data.Map as Data_Map
import Numeric (showHex, readHex)

-- Project imports

import ALU
import Arch_Defs
import GPR_File
import FPR_File
import CSR_File
import Mem_Ops
import Memory
import MMIO
import Address_Map

-- ================================================================
-- Architectural State data structure.
-- This is a private internal representation that can be changed at
-- will; only the exported API can be used by clients.
                                                          -- \begin_latex{Machine_State}
data Machine_State =
  Machine_State { -- Architectural state
                  f_pc   :: Integer,
                  f_gprs :: GPR_File,
                  f_fprs :: FPR_File,
                  f_csrs :: CSR_File,
                  f_priv :: Priv_Level,

                  -- Memory and mory mapped IO
                  f_mem  :: Mem,
                  f_mmio :: MMIO,

                  -- Implementation options

                  -- Legal memory addresses: list of (addr_start, addr_lim)
                  f_mem_addr_ranges :: [(Integer, Integer)],

                  -- For convenience and debugging only; no semantic relevance
                  f_rv                 :: RV,   -- redundant copy of info in CSR MISA
                  f_run_state          :: Run_State,
                  f_last_instr_trapped :: Bool,
                  f_verbosity          :: Int
                }
                                                          -- \end_latex{Machine_State}
data Run_State = Run_State_Running
               | Run_State_WFI        -- Paused waiting for interrupt
  deriving (Eq, Show)

mstate_print :: String -> Machine_State -> IO ()
mstate_print  indent  mstate = do
  let pc   = f_pc    mstate
      gprs = f_gprs  mstate
      fprs = f_fprs  mstate
      csrs = f_csrs  mstate
      priv = f_priv  mstate

      rv        = f_rv    mstate
      run_state = f_run_state  mstate

      xlen      = if (rv == RV32) then 32 else 64
  
  putStrLn (indent ++ show rv ++ " pc:" ++ showHex pc " priv:" ++ show priv)
  print_GPR_File  indent  xlen  gprs
  print_FPR_File  indent  64    fprs    -- FPR always stored as 64-bit
  print_CSR_File  indent  rv  csrs
  -- We do not print memory or MMIO
  putStrLn (indent ++ (show run_state))

-- ================================================================
-- API to create, read/write components of the Architectural State

                                                              -- \begin_latex{Machine_State_constructor}
-- Make a Machine_State, given initial PC and memory contents
mkMachine_State :: RV ->                      -- Initial RV32/RV64
                   Integer ->                 -- Initial value of misa
                   Integer ->                 -- Initial value of PC
                   [(Integer,Integer)] ->     -- List of legal memory addresses
                   ([(Integer, Integer)]) ->  -- Initial mem contents (addr-&-byte list)
                   Machine_State              -- result
mkMachine_State  rv  misa  initial_PC  addr_ranges  addr_byte_list =
  let
    mstate = Machine_State {f_pc   = initial_PC,
                            f_gprs = mkGPR_File,
                            f_fprs = mkFPR_File,
                            f_csrs = mkCSR_File  rv  misa,
                            f_priv = m_Priv_Level,

                            f_mem             = mkMem  addr_byte_list,
                            f_mmio            = mkMMIO,
                            f_mem_addr_ranges = addr_ranges,

                            f_rv                 = rv,
                            f_run_state          = Run_State_Running,
                            f_last_instr_trapped = False,
                            f_verbosity          = 0
                           }
  in
    mstate
                                                              -- \end_latex{Machine_State_constructor}
-- ================================================================
-- read/write PC                                                 \begin_latex{PC_access}

mstate_pc_read :: Machine_State -> Integer
mstate_pc_read  mstate = f_pc mstate

mstate_pc_write :: Machine_State -> Integer -> Machine_State
mstate_pc_write  mstate  val = mstate { f_pc = val }
                                                              -- \end_latex{PC_access}
{-# INLINE mstate_pc_read #-}
{-# INLINE mstate_pc_write #-}

-- read/write current privilege level

mstate_priv_read :: Machine_State -> Priv_Level
mstate_priv_read  mstate = f_priv  mstate

mstate_priv_write :: Machine_State -> Priv_Level -> Machine_State
mstate_priv_write  mstate  priv = mstate { f_priv = priv }

{-# INLINE mstate_priv_read #-}
{-# INLINE mstate_priv_write #-}

-- ================================================================
-- read/write RV, xlen

mstate_rv_read :: Machine_State -> RV
mstate_rv_read  mstate = f_rv  mstate

mstate_rv_write :: Machine_State -> RV -> Machine_State
mstate_rv_write  mstate  rv = mstate { f_rv = rv }

mstate_xlen_read :: Machine_State -> Int
mstate_xlen_read  mstate | (f_rv  mstate == RV32) = 32
                         | (f_rv  mstate == RV64) = 64

{-# INLINE mstate_rv_read #-}
{-# INLINE mstate_rv_write #-}
{-# INLINE mstate_xlen_read #-}

-- ================================================================
-- read/write GPRs

mstate_gpr_read :: Machine_State -> GPR_Addr -> Integer
mstate_gpr_read  mstate  reg = gpr_read (f_gprs mstate)  reg

mstate_gpr_write :: Machine_State -> GPR_Addr -> Integer -> Machine_State
mstate_gpr_write  mstate  reg  val =
  let
    gprs    = f_gprs  mstate
    gprs'   = gpr_write  gprs  reg  val
    mstate' = mstate { f_gprs = gprs' }
  in
    mstate'

{-# INLINE mstate_gpr_read #-}
{-# INLINE mstate_gpr_write #-}

-- ================================================================
-- read/write FPRs

mstate_fpr_read :: Machine_State -> FPR_Addr -> Integer
mstate_fpr_read    mstate           reg       = fpr_read (f_fprs mstate)  reg

mstate_fpr_write :: Machine_State -> FPR_Addr -> Integer -> Machine_State
mstate_fpr_write    mstate           reg         val =
  let
    fprs    = f_fprs  mstate
    fprs'   = fpr_write  fprs  reg  val
    mstate' = mstate { f_fprs = fprs' }
  in
    mstate'

{-# INLINE mstate_fpr_read #-}
{-# INLINE mstate_fpr_write #-}

-- ================================================================
-- read/write CSRs
-- Assumes CSR exists and access is legal

-- Checks permissions (None, RO, RW) of a csr_addr at a given privilege level

mstate_csr_permission :: Machine_State -> Priv_Level -> CSR_Addr -> CSR_Permission
mstate_csr_permission  mstate  priv  csr_addr =
  csr_permission  (f_csrs  mstate)  priv  csr_addr

mstate_csr_read :: Machine_State -> CSR_Addr -> Integer
mstate_csr_read  mstate  csr_addr = csr_read  (f_rv  mstate)  (f_csrs  mstate)  csr_addr

mstate_csr_write :: Machine_State -> CSR_Addr -> Integer -> Machine_State
mstate_csr_write  mstate  csr_addr  value =
  let
    csr_file' = csr_write  (f_rv  mstate)  (f_csrs  mstate)  csr_addr  value
    mstate'   = mstate { f_csrs = csr_file' }
  in
    mstate'

{-# INLINE mstate_csr_permission #-}
{-# INLINE mstate_csr_read #-}
{-# INLINE mstate_csr_write #-}

-- ----------------
-- Update the CSR by accruing the new value. Do not owerwrite
-- This behaviour of accruing results is unique to the FCSR.

mstate_csr_update   :: Machine_State    -> CSR_Addr -> Integer  -> Machine_State
mstate_csr_update      mstate              csr_addr    new_val  =
  let
    old_val     = mstate_csr_read  mstate  csr_addr

    -- accrue new value, do not overwrite
    val'        = old_val .|. new_val

    mstate'     = mstate_csr_write  mstate  csr_addr  val'
  in
    mstate'

{-# INLINE mstate_csr_update #-}

-- ================================================================
-- Memory access
-- API functions use address to invoke either memory or memory-mapped I/O devices
-- Note: we compute a new mem state even on reads since they can have side-effects
--   - Memory may change state of PTEs, memory-model tracking, cache coherence, ...
--   - I/O devices may also change device-internal state)

-- ----------------------------------------------------------------
-- Check if the memory address is supported

is_supported_addr :: Machine_State -> InstrField -> Integer -> Bool
is_supported_addr  mstate  funct3  addr =
  let
    size | (funct3 == funct3_LB)  = 1
         | (funct3 == funct3_LBU) = 1
         | (funct3 == funct3_LH)  = 2
         | (funct3 == funct3_LHU) = 2
         | (funct3 == funct3_LW)  = 4
         | (funct3 == funct3_LWU) = 4
         | (funct3 == funct3_LD)  = 8
    addr_lim = addr + size

    check [] = False
    check ((astart,alim):ranges) | ((addr >= astart) && (addr_lim <= alim)) = True
                                 | True                                     = check  ranges

    addr_ranges = f_mem_addr_ranges  mstate
  in
    check  addr_ranges

{-# INLINE is_supported_addr #-}

-- ----------------------------------------------------------------
-- Memory and MMIO reads

mstate_mem_read :: Machine_State -> Exc_Code ->            InstrField -> Integer -> (Mem_Result, Machine_State)
mstate_mem_read    mstate           exc_code_access_fault  funct3        addr =
  if not (is_supported_addr  mstate  funct3  addr)
  then
    -- Memory access fault
    let
      load_result = Mem_Result_Err  exc_code_access_fault
    in
      (load_result, mstate)
      -- Note: use the following return value instead to force an abort on unsupported address access
      -- (seq (error ("mem_read: unsupported address " ++ show addr))
      --  (load_result, mstate))

  else if not (is_IO_addr  addr) then
    -- Memory access
    let (load_result, mem') = mem_read  (f_mem mstate)  funct3  addr
        mstate' = (mstate  { f_mem = mem'})
    in
      (load_result, mstate')

  else
    -- MMIO access
    let (load_result, mmio') = mmio_read  (f_mmio mstate)  funct3  addr
    in
      (load_result, (mstate { f_mmio = mmio'}))

{-# INLINE mstate_mem_read #-}

-- ----------------------------------------------------------------
-- Memory and MMIO writes

mstate_mem_write :: Machine_State -> InstrField -> Integer -> Integer -> (Mem_Result, Machine_State)
mstate_mem_write  mstate  funct3  addr  val =
  if not (is_supported_addr  mstate  funct3  addr)
  then
    -- Memory access fault
    let
      load_result = Mem_Result_Err  exc_code_store_AMO_access_fault
    in
      (load_result, mstate)
      -- Note: use the following return value instead to force an abort on unsupported address access
      -- (seq (error ("mem_write: unsupported address " ++ show addr))
      --  (load_result, mstate))

  else if not (is_IO_addr  addr) then
    -- Memory access
    let (store_result, mem') = mem_write  (f_mem mstate)  funct3  addr  val
    in
      (store_result, mstate { f_mem = mem'})

  else
    -- MMIO access
    let
      (store_result, mmio') = mmio_write  (f_mmio  mstate)  funct3  addr  val
      mstate1               = mstate { f_mmio = mmio' }
    in
      (store_result, mstate1)

{-# INLINE mstate_mem_write #-}

-- ----------------------------------------------------------------
-- Atomic Memory Ops

mstate_mem_amo :: Machine_State ->
                     Integer       ->    -- addr
                     InstrField    ->    -- funct3
                     InstrField    ->    -- msbs5
                     InstrField    ->    -- aq
                     InstrField    ->    -- rl
                     Integer       ->    -- store-val
                     (Mem_Result, Machine_State)
mstate_mem_amo  mstate  addr  funct3  msbs5  aq  rl  st_val =
  if not (is_supported_addr  mstate  funct3  addr)
  then
    -- Memory access fault
    let
      load_result = Mem_Result_Err  exc_code_store_AMO_access_fault
    in
      (load_result, mstate)

  else if not (is_IO_addr  addr) then
    -- Memory access
    let (load_result, mem') = mem_amo  (f_mem mstate)  addr  funct3  msbs5  aq  rl  st_val
    in
      (load_result, mstate { f_mem = mem'})

  else
    -- MMIO access
    let (load_result, mmio') = mmio_amo  (f_mmio mstate)  addr  funct3  msbs5  aq  rl  st_val
    in
      (load_result, (mstate { f_mmio = mmio'}))

{-# INLINE mstate_mem_amo #-}

-- ----------------------------------------------------------------
-- Memory fences
-- TODO: currently no-ops; fixup when we handle concurrency

mstate_mem_fence  :: Machine_State -> Machine_State
mstate_mem_fence  mstate = mstate

mstate_mem_fence_i  :: Machine_State -> Machine_State
mstate_mem_fence_i  mstate = mstate

mstate_mem_sfence_vma  :: Machine_State -> Integer -> Integer -> Machine_State
mstate_mem_sfence_vma  mstate  rs1_val  rs2_val = mstate

{-# INLINE mstate_mem_fence #-}
{-# INLINE mstate_mem_fence_i #-}
{-# INLINE mstate_mem_sfence_vma #-}

-- ================================================================
-- Check if an interrupt is pending to resume from WFI state.
-- Note: resuming from WFI does not actually take the interrupt, just
-- resumes at the instruction following WFI (which may, in turn, take
-- the interrupt).  Thus, this condition is typically weaker than
-- condition for taking an interrupt (see csr_wfi_resume).

mstate_wfi_resume :: Machine_State -> Bool
mstate_wfi_resume    mstate =
  let
    mip = mstate_csr_read  mstate  csr_addr_mip
    mie = mstate_csr_read  mstate  csr_addr_mie
  in
    csr_wfi_resume  mip  mie

-- ================================================================
-- Simulation aids

-- ----------------------------------------------------------------
-- I/O: enq console input into machine state (CPU <- MMIO <- UART <- tty)

mstate_mem_enq_console_input :: Machine_State -> String -> Machine_State
mstate_mem_enq_console_input  mstate  s =
  let
    mmio                    = f_mmio  mstate
    mmio'                   = mmio_enq_console_input  mmio  s
    mstate'                 = mstate { f_mmio = mmio' }
  in
    mstate'

{-# INLINE mstate_mem_enq_console_input #-}

-- ----------------------------------------------------------------
-- I/O: deq console output from machine state (CPU -> MMIO -> UART -> tty)

mstate_mem_deq_console_output :: Machine_State -> (String, Machine_State)
mstate_mem_deq_console_output  mstate =
  let
    mmio                    = f_mmio  mstate
    (console_output, mmio') = mmio_deq_console_output  mmio
    mstate'                 = if (console_output == "") then mstate
                              else mstate { f_mmio = mmio' }
  in
    (console_output, mstate')

{-# INLINE mstate_mem_deq_console_output #-}

-- ----------------------------------------------------------------
-- I/O: Read all console input (for debugging etc.)

mstate_mem_all_console_input :: Machine_State -> (String, String)
mstate_mem_all_console_input  mstate =
  let
    mmio = f_mmio  mstate
  in
    mmio_all_console_input  mmio

-- ----------------------------------------------------------------
-- I/O: Read all console output (for debugging etc.)

mstate_mem_all_console_output :: Machine_State -> (String, String)
mstate_mem_all_console_output  mstate =
  let
    mmio = f_mmio  mstate
  in
    mmio_all_console_output  mmio

-- I/O: Tick
--     incr CSR.MCYCLE
--     incr MMIO.MTIME

-- ----------------------------------------------------------------
-- Advance IO devices (which ``run'' concurrently with the CPU)

mstate_io_tick :: Machine_State -> Machine_State
mstate_io_tick  mstate =
  let
    rv    = f_rv    mstate
    csrs  = f_csrs  mstate
    mmio  = f_mmio  mstate

    -- Tick CSR.MCYCLE
    csrs1  = (let
                 mcycle = csr_read   rv  csrs  csr_addr_mcycle
                 csrs'  = csr_write  rv  csrs  csr_addr_mcycle  (mcycle + 1)
              in
                 csrs')

    -- Tick memory-mapped location MMIO.MTIME
    mmio1  = mmio_tick_mtime  mmio

    -- Set MIP.MEIP, MIP.MTIP and MIP.MSIP if these interrupts are present
    mip_old = csr_read   rv  csrs1  csr_addr_mip
    eip_old = testBit  mip_old  mip_meip_bitpos
    tip_old = testBit  mip_old  mip_mtip_bitpos
    sip_old = testBit  mip_old  mip_msip_bitpos

    (eip_new, tip_new, sip_new) = mmio_has_interrupts  mmio1

    csrs2 = if ((eip_new == eip_old) && (tip_new == tip_old) && (sip_new == sip_old)) then
              csrs1
            else
              (let
                  mip1 = if (eip_new) then (mip_old  .|.  (shiftL  1  mip_meip_bitpos))
                         else              (mip_old  .&.  (complement (shiftL  1  mip_meip_bitpos)))

                  mip2 = if (tip_new) then (mip1  .|.  (shiftL  1  mip_mtip_bitpos))
                         else              (mip1  .&.  (complement (shiftL  1  mip_mtip_bitpos)))

                  mip3 = if (sip_new) then (mip2  .|.  (shiftL  1  mip_msip_bitpos))
                         else              (mip2  .&.  (complement (shiftL  1  mip_msip_bitpos)))
               in
                  csr_write  rv  csrs1  csr_addr_mip  mip3)

    mstate1 = mstate { f_mmio = mmio1, f_csrs = csrs2 }
  in
    mstate1

{-# INLINE mstate_io_tick #-}

-- ----------------------------------------------------------------
-- I/O: convenience back-door function to read mtime directly
-- (instead of using mstate_mem_read, which can raise exceptions etc.)

mstate_mem_read_mtime :: Machine_State -> Integer
mstate_mem_read_mtime  mstate = mmio_read_mtime  (f_mmio  mstate)

{-# INLINE mstate_mem_read_mtime #-}

-- ----------------
-- For debugging only
-- Returns number of entries in the Data.Map

mstate_mem_num_entries :: Machine_State -> Int
mstate_mem_num_entries  mstate =
  let
    mem = f_mem  mstate
  in
    mem_num_entries  mem

-- ================================================================
-- read/write misc debug convenience

mstate_run_state_read :: Machine_State -> Run_State
mstate_run_state_read    mstate = f_run_state  mstate

{-# INLINE mstate_run_state_read #-}

mstate_run_state_write :: Machine_State -> Run_State -> Machine_State
mstate_run_state_write    mstate           run_state = mstate { f_run_state = run_state }

mstate_last_instr_trapped_read :: Machine_State -> Bool
mstate_last_instr_trapped_read    mstate = f_last_instr_trapped mstate

{-# INLINE mstate_last_instr_trapped_read #-}

mstate_last_instr_trapped_write :: Machine_State -> Bool -> Machine_State
mstate_last_instr_trapped_write    mstate           trapped = mstate { f_last_instr_trapped = trapped }

mstate_verbosity_read :: Machine_State -> Int
mstate_verbosity_read    mstate = f_verbosity mstate

{-# INLINE mstate_verbosity_read #-}

mstate_verbosity_write :: Machine_State -> Int -> Machine_State
mstate_verbosity_write    mstate           verbosity = mstate { f_verbosity = verbosity }

-- ================================================================

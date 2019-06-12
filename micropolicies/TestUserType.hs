{-# LANGUAGE PartialTypeSignatures, ScopedTypeVariables, TupleSections, FlexibleInstances, MultiParamTypeClasses, NamedFieldPuns #-}

module TestUserType where

-- From Haskell libraries
import Control.Arrow (second, (***))
import Control.Exception.Base (assert)
import Control.Monad.Reader

import Data.Bits
import Data.List (zip4,unzip4)
import Data.Maybe
import qualified Data.List as Data_List
import qualified Data.Map.Strict as Data_Map
import qualified Data.Set as Data_Set
import Data.Set (Set)
import Debug.Trace

import Test.QuickCheck

import Text.PrettyPrint (Doc, (<+>), ($$))
import qualified Text.PrettyPrint as P

-- from policy-tool
import qualified AST

-- From /src
import Arch_Defs
import Bit_Utils
import CSR_File
import Encoder
import Forvis_Spec_I
import Forvis_Spec_Instr_Fetch
import GPR_File
import Machine_State
import Memory

-- From .
import Gen
import Run_Program_PIPE
import PIPE
import Printing
import Terminal 

------------------------------------------------------------------------------------------
-- Generation

-- GPR's are hard coded to be [0..31], but we only use a couple of them
maxReg = 3

-- Generate a random register for source
genSourceReg :: Machine_State -> Gen GPR_Addr
genSourceReg ms =
  choose (0, maxReg)

-- Generate a target register GPR
-- For now, just avoid R0
genTargetReg :: Machine_State -> Gen GPR_Addr
genTargetReg ms =
  choose (1, maxReg)

-- Generate an immediate up to number
-- Multiple of 4
genImm :: Integer -> Gen InstrField
-- -- (Hmm - Why did we never generate 0 at some point?)
-- genImm n = (4*) <$> choose (1, n `div` 4)   
genImm n = (4*) <$> choose (0, n `div` 4)

groupRegisters :: PolicyPlus -> GPR_File ->
                  ([(GPR_Addr, Integer, Integer, Integer)],
                   [GPR_Addr])
groupRegisters pplus (GPR_File rs) =
  -- Assuming that the register files are same length and they have no holes
  let regs = Data_Map.assocs rs

      validData (reg_id,reg_content) 
        | reg_content >= dataMemLow pplus &&
          reg_content <= dataMemHigh pplus =
           Just (reg_id, reg_content, 0, dataMemHigh pplus - reg_content)
        | reg_content == 0 =
        -- We can allow a 0 register by adding at least 4
           Just (reg_id, 0, dataMemLow pplus, dataMemHigh pplus)
        | otherwise =
           Nothing
        
      dataRegs    = map (fromJust) $ filter (isJust) $ map validData regs
      arithRegs   = map fst regs
  in (dataRegs, arithRegs)

assignmentTag :: TagSet
assignmentTag = Data_Map.fromList [(AST.QTag ["userType","Assignment"],Nothing)]

genInstr :: PolicyPlus -> Machine_State -> Gen (Instr_I, TagSet)
genInstr pplus ms =
  let (dataRegs, arithRegs) = groupRegisters pplus (f_gprs ms)
      onNonEmpty [] _= 0
      onNonEmpty _ n = n
  in 
  frequency [ (onNonEmpty arithRegs 1,
               do -- ADDI
                  rs <- elements arithRegs
                  rd <- genTargetReg ms
                  imm <- genImm (dataMemHigh pplus)
                  -- (Old comment? "Need to figure out what to do with Malloc")
                  return (ADDI rd rs imm, emptyInstTag pplus))
            , (onNonEmpty dataRegs 3,
               do -- LOAD
                  (rd,content, min_imm,max_imm) <- elements dataRegs
                  rs <- genTargetReg ms
                  imm <- (min_imm+) <$> genImm (max_imm - min_imm)
                  return (LW rd rs imm, emptyInstTag pplus)
              )
            , (onNonEmpty dataRegs 3 * onNonEmpty arithRegs 1,
               do -- STORE
                  (rd,content, min_imm,max_imm) <- elements dataRegs
                  rs <- genTargetReg ms
                  imm <- (min_imm+) <$> genImm (max_imm - min_imm)
                  tag <- frequency
                            [(3, pure $ emptyInstTag pplus),
                             (1, pure $ assignmentTag)]
                  return (SW rd rs imm, tag))
            , (onNonEmpty arithRegs 1,
               do -- ADD
                  rs1 <- elements arithRegs
                  rs2 <- elements arithRegs
                  rd <- genTargetReg ms
                  return (ADD rd rs1 rs2, emptyInstTag pplus))
            , (1, do -- JAL x0
                  let tag = emptyInstTag pplus
                  -- the offset is in multiples of 2 bytes, but we want 32-bit
                  -- aligned destinations, so we use only even offsets.  We
                  -- pick a destination within a range of 50 instructions
                  -- backwards or forwards.
                  off <- choose (-25,25)
                  return (JAL 0 (2*off), emptyInstTag pplus))
            ]

randInstr :: PolicyPlus -> Machine_State -> Gen (Instr_I, TagSet)
randInstr pplus ms =
  frequency [ (1, do -- ADDI
                  rs <- genSourceReg ms
                  rd <- genTargetReg ms
                  imm <- genImm 4
                  return (ADDI rd rs imm, emptyInstTag pplus))
            , (1, do -- LOAD
                  rs <- genSourceReg ms
                  rd <- genTargetReg ms
                  imm <- genImm 4
                  let tag = emptyInstTag pplus                  
                  return (LW rd rs imm, tag))
            , (1, do -- STORE
                  rs <- genSourceReg ms
                  rd <- genTargetReg ms
                  imm <- genImm 4
                  let tag = emptyInstTag pplus
                  return (SW rd rs imm, tag))
            , (1, do -- ADD
                  rs1 <- genSourceReg ms
                  rs2 <- genSourceReg ms
                  rd <- genTargetReg ms
                  let tag = emptyInstTag pplus
                  return (ADD rd rs1 rs2, tag))
            , (1, do -- JAL x0
                  let tag = emptyInstTag pplus
                  -- the offset is in multiples of 2 bytes, but we want 32-bit
                  -- aligned destinations, so we use only even offsets.  We
                  -- pick a destination within a range of 50 instructions
                  -- backwards or forwards.
                  off <- choose (-25,25)
                  return (JAL 0 (2*off), emptyInstTag pplus))
            ]

genMTagM :: Gen TagSet
genMTagM = return Data_Map.empty

genDataMemory :: PolicyPlus -> Gen (Mem, MemT)
genDataMemory pplus = do
  let idx = [dataMemLow pplus, (dataMemLow pplus)+4..(dataMemHigh pplus)]
  combined <- mapM (\i -> do d <- genImm $ dataMemHigh pplus    -- BCP: This always puts 4 in every location!
                             t <- genMTagM
                             return ((i, d),(i,t))) idx
  let (m,pm) = unzip combined
  return (Mem (Data_Map.fromList m) Nothing, MemT $ Data_Map.fromList pm)

setInstrI :: Machine_State -> Instr_I -> Machine_State
setInstrI ms i =
  ms {f_mem = (f_mem ms) { f_dm = Data_Map.insert (f_pc ms) (encode_I RV32 i) (f_dm $ f_mem ms) } }

setInstrTagI :: Machine_State -> PIPE_State -> TagSet -> PIPE_State
setInstrTagI ms ps it =
  ps {p_mem = ( MemT $ Data_Map.insert (f_pc ms) (it) (unMemT $ p_mem ps) ) }

genByExec :: PolicyPlus -> Int -> Machine_State -> PIPE_State -> Set GPR_Addr -> Gen (Machine_State, PIPE_State, Set GPR_Addr)
genByExec pplus 0 ms ps instrlocs = return (ms, ps, instrlocs)
genByExec pplus n ms ps instrlocs
  -- Check if an instruction already exists
  | Data_Map.member (f_pc ms) (f_dm $ f_mem ms) =
    case fetch_and_execute pplus ms ps of
      Right (ms'', ps'', _) ->
        genByExec pplus (n-1) ms'' ps'' instrlocs
      Left err ->
        -- trace ("Warning: Fetch and execute failed with " ++ show n
        --        ++ " steps remaining and error: " ++ show err) $
        return (ms, ps, instrlocs)
  | otherwise = do
--    (is, it) <- randInstr pplus ms
    (is,it) <- genInstr pplus ms
    let ms' = setInstrI ms is
        ps' = setInstrTagI ms ps it
    case -- traceShow ("Instruction generated...", is) $
         fetch_and_execute pplus ms' ps' of
      Right (ms'', ps'', _) ->
        -- trace "Successful execution" $
        genByExec pplus (n-1) ms'' ps'' (Data_Set.insert (f_pc ms') instrlocs)
      Left err ->
--        trace ("Warning: Fetch and execute failed with "
--               ++ show n ++ " steps remaining and error: " ++ show err) $
        return (ms', ps', (Data_Set.insert (f_pc ms') instrlocs))

updRegs :: GPR_File -> Gen GPR_File
updRegs (GPR_File rs) = do
  [d1, d2, d3] <- replicateM 3 $ genImm 40
  let rs' :: Data_Map.Map Integer Integer = Data_Map.insert 1 d1 $ Data_Map.insert 2 d2 $ Data_Map.insert 3 d3 rs
  return $ GPR_File rs'

mkPointerTagSet pplus c = fromExt [("heap.Pointer", Just c)]

genMachine :: PolicyPlus -> Gen MState
genMachine pplus = do
  -- registers
  (mem,pmem) <- genDataMemory pplus
  let ms = initMachine {f_mem = mem}
      ps = (init_pipe_state pplus){p_mem = pmem}
      ms2 = setInstrI ms (JAL 0 1000)
      ps' = setInstrTagI ms ps (emptyInstTag pplus)  -- Needed??

  rs' <- updRegs $ f_gprs ms2
  let ms' = ms2 {f_gprs = rs'}
  
  (ms_fin, ps_fin, instrlocs) <- genByExec pplus maxInstrsToGenerate ms' ps' Data_Set.empty

  let final_mem = f_dm $ f_mem ms_fin
      res_mem = foldr (\a mem -> Data_Map.insert a (fromJust $ Data_Map.lookup a final_mem) mem) (f_dm $ f_mem ms') instrlocs
      ms_fin' = 
        ms' {f_mem = (f_mem ms') { f_dm = res_mem } }  

      final_pmem = unMemT $ p_mem ps_fin
      res_pmem = foldr (\a pmem -> Data_Map.insert a (fromJust $ Data_Map.lookup a final_pmem) pmem) (unMemT $ p_mem ps') instrlocs
      ps_fin' =
        ps' {p_mem = MemT res_pmem}

  return $ M (ms_fin', ps_fin')

genMState_ :: PolicyPlus -> Gen MState
genMState_ pplus = genMachine pplus

------------------------------------------------------------------------------------------
-- Shrinking

-- Tag shrinking basically amounts to shrinking the colors
-- of things to C 0. Assuming that C 0 is always reachable.
-- We can't change the Tag type. We can't change the Color
-- arbitrarily.
shrinkColor :: Color -> [Color]
shrinkColor (0) = []
shrinkColor (1) = [0]
shrinkColor (n) = [0,n-1]

shrinkTag :: TagSet -> [TagSet]
shrinkTag t =
  case toExt t of
    [("heap.Alloc", Nothing), ("heap.Instr", Nothing)] ->
      [fromExt [("heap.Instr", Nothing)]]
    [("heap.Pointer", Just cp)] ->
      [fromExt [("heap.Pointer", Just cp')] | cp' <- shrinkColor cp]
    [("heap.Cell", Just cc), ("heap.Pointer", Just cp)] ->
         [fromExt [("heap.Cell", Just cc'), ("heap.Pointer", Just cp )] | cc' <- shrinkColor cc]
      ++ [fromExt [("heap.Cell", Just cc),  ("heap.Pointer", Just cp')] | cp' <- shrinkColor cp]
    _ -> []


shrinkRegister :: PolicyPlus -> (Integer, TagSet) -> [(Integer, TagSet)]
shrinkRegister pplus (d,t) = [(d',t') | d' <- shrink d, t' <- shrinkTag t]

shrinkVector :: (a -> [a]) -> [a] -> [[a]]
shrinkVector f []    = []
shrinkVector f (h:t) = map (:t) (f h) ++ map (h:) (shrinkVector f t)

shrinkGPR :: PolicyPlus -> (GPR_File, GPR_FileT) -> [(GPR_File, GPR_FileT)]
shrinkGPR pplus (GPR_File d, GPR_FileT t) =
  let combined :: [((GPR_Addr, GPR_Val), (InstrField, TagSet))]
      combined = zip (Data_Map.assocs d) (Data_Map.assocs t)
   in
  [ (GPR_File $ Data_Map.fromList d1', GPR_FileT $ Data_Map.fromList t1')
  | (d1',t1') <- map unzip $ shrinkVector shrinkR combined
  ]
  where shrinkR :: ((GPR_Addr, GPR_Val), (InstrField, TagSet))
                -> [((GPR_Addr, GPR_Val), (InstrField, TagSet))]
        shrinkR ((i1,v1),(j1,l1)) =
             [ ((i1,v'),(j1,l1)) | v' <- shrink v1 ]
          ++ [ ((i1,v1),(j1,l')) | l' <- shrinkTag l1 ]

-- To shrink an instruction, try converting it to a noop (ADD 0 0 0)
shrinkInstr :: Instr_I -> [Instr_I]
shrinkInstr (ADD 0 0 0)  = []
-- Do not shrink the initial JAL
shrinkInstr (JAL 0 1000) = []
shrinkInstr _ = [ADD 0 0 0]

shrinkMem :: PolicyPlus -> (Mem, MemT) -> [(Mem, MemT)]
shrinkMem pplus (Mem {f_dm, f_reserved_addr}, MemT tagMap) =
  let mem  = Data_Map.assocs f_dm
      tags = Data_Map.assocs tagMap

      isData  i = i >= dataMemLow pplus && i <= dataMemHigh pplus
      isInstr i = i == 0 || i >= instrLow pplus
 
      shrinkMemLoc :: (Integer, Integer, TagSet) -> [ (Integer, Integer, TagSet) ]
      shrinkMemLoc (loc,val,tag)
        | isInstr loc =
          case (decode_I RV32 val) of
            (Just i) ->
              [ (loc,val',tag) | val' <- encode_I RV32 <$> shrinkInstr i]
            _ -> error "Instruction can't be decoded while shrinking"
        | otherwise =
              -- shrink data
              [ (loc,val',tag) | val' <- shrink val ]
              -- or shrink dag
           ++ [ (loc,val,tag') | tag' <- shrinkTag tag ]
 
      shrinkMemAux :: [(Integer,Integer,TagSet)]
                   -> [[(Integer,Integer,TagSet)]]
      shrinkMemAux [] = []
      shrinkMemAux (m:ms) =
        -- Shrink Current memory location and rebuild mem
        [ m':ms | m' <- shrinkMemLoc m ]
        ++
        -- Keep current memory location and shrink something later on
        [ m:ms' | ms' <- shrinkMemAux ms ]

      recreateMem :: [(Integer, Integer, TagSet)] -> (Mem,MemT)
      recreateMem m = (Mem (Data_Map.fromList $ map (\(l,v,_) -> (l,v)) m)
                           f_reserved_addr,
                       MemT (Data_Map.fromList $ map (\(l,_,t) -> (l,t)) m))
                          
        
  in map recreateMem $ shrinkMemAux $
       zipWith (\(l,v) (l',t) ->
                     if l /= l' then error "Mem and tags don't match"
                                else (l,v,t)) mem tags
               

shrinkMState_ :: PolicyPlus -> MState -> [MState]
shrinkMState_ pplus (M (m,p)) =
     [ M (m{f_mem = mem'},p{p_mem = pmem'})
     | (mem', pmem') <- shrinkMem pplus (f_mem m, p_mem p) ]
  ++ [ M (m{f_gprs = gpr'},p{p_gprs = pgpr'})
     | (gpr', pgpr') <- shrinkGPR pplus (f_gprs m, p_gprs p) ]


------------------------------------------------------------------------------------------
-- Top-level write once property

-- Check that, for each address in the list, the two memories agree on the
-- value.
unchanged :: [Integer] -> Machine_State -> Machine_State -> Property
unchanged addrs ms1 ms2 = conjoin $ map check_addr addrs
  where
    mem1, mem2 :: Mem
    mem1 = f_mem ms1
    mem2 = f_mem ms2
    
    check_addr :: Integer -> Property
    check_addr addr =
      label ("Assigned addresses unchanged") $ property $
           Data_Map.lookup addr (f_dm mem1)
        == Data_Map.lookup addr (f_dm mem2)
  
{- "fixed" is a list of memory locations that have been "assigned".
   We check at each instruction that the data in these places has not changed.
 -}
prop_writeonce pplus count maxcount trace fixed ms@(M (m,p)) =
--  trace (P.render $ prettyMState pplus ms) $
  let run_state = mstate_run_state_read m
      m' = mstate_io_tick m
      trace' = (m,p):trace
  in
  if count >= maxcount then
    label "Out of gas" $ property True
  else if run_state /= Run_State_Running then
    label (show run_state) $ property True
  else
    case fetch_and_execute pplus m' p of
      Right (mr,pr,minst) ->
        -- Check that no fixed addresses have changed.
             whenFail (do putStrLn $ "A memory value that was previously "
                                  ++ "Assigned has changed!"
                          let finalTrace = reverse $ (mr,pr):trace'
                          printTrace pplus finalTrace)
                      (unchanged fixed m mr)
        -- Recurse, extending fixed set if this instruction assigned
        .&&. prop_writeonce pplus (count+1) maxcount trace' newFixed (M (mr,pr))
        where
          newFixed :: [Integer]
          newFixed =
            -- find code tags, and instruction
            case (minst, Data_Map.lookup (mstate_pc_read m) (unMemT $ p_mem p)) of
              (Nothing,_) -> fixed
              (_,Nothing) -> error $ "untagged instruction "
                                  ++ show (mstate_pc_read m)
              (Just u32, Just code_tags) ->
                -- decode instruction and find code tagscheck if this code assign tag
                case (decode_I RV32 u32,
                      Data_Map.lookup (AST.QTag ["userType","Assignment"]) code_tags)
                of
                  -- invalid instruction
                  (Nothing,_) -> error "Invalid instruction."
                  -- code doesn't have assignment tag, so don't add to fixed
                  (Just i,Nothing) -> fixed
                  -- code does have assignment tag, find address stored to
                  (Just i,Just _) ->
                    case find_maddr i m of
                      MUStore addr -> addr:fixed
                      _ -> error $ "Assignment tag encountered on non-store instruction " ++ show i
      Left s ->
        label ("PIPE trap " ++ s) $ property True
  

maxInstrsToGenerate :: Int
maxInstrsToGenerate = 10

prop_ :: PolicyPlus -> MState -> Property
prop_ pplus ms = prop_writeonce pplus 0 maxInstrsToGenerate [] [] ms

------------------------------------------------------------------------------------------
-- The user type policy
  
load_policy = do
  ppol <- load_pipe_policy "userType.userTypePol"
  let pplus = PolicyPlus
        { policy = ppol
        , initGPR = Data_Map.empty
        , initMem = Data_Map.empty
        , initPC = Data_Map.empty
        , emptyInstTag = Data_Map.empty
        , dataMemLow = 4
        , dataMemHigh = 20  -- Was 40, but that seems like a lot! (8 may be too little!)
        , instrLow = 1000
        , shrinkMState = shrinkMState_
        , genMState = genMState_
        , prop = prop_
        }
  return pplus


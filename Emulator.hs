{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}


module Main where

import Prelude hiding (catch)

import Data.Char
import Data.Map (Map)
import Data.Bits
import qualified Data.Map as Map
import Data.Data
import Data.Sequence
import Data.Foldable

data CapType = TLin | TNon | TRev | TSealed | TSealedRet Reg | TUninit 
    deriving (Eq, Show)

type Addr = Int

data Perm = PermNA | PermR | PermRW | PermRX | PermRWX
    deriving (Eq, Show)

data Reg = Pc | Epc | Ret | GPR Int
    deriving (Eq, Show, Typeable, Data)

data MWord = Cap {
    capType :: CapType,
    capBase :: Addr,
    capEnd :: Addr,
    capCursor :: Addr,
    capPerm :: Perm,
    capNode :: Int 
} | Value Int | Inst Instruction
    deriving (Show)

data RegFile = RegFile {
    pc :: MWord,
    domId :: MWord,
    epc :: MWord,
    ret :: MWord,
    gprs :: Seq MWord
} deriving (Show)

data RevNodeType = RNNonLin | RNLin
    deriving (Show, Eq)

data RevNode = RevNode Int RevNodeType | RevNodeRoot | RevNodeNull
    deriving (Show, Eq)

newtype RevTree = RevTree (Seq RevNode)
    deriving (Show)

data Immediate = Integer Int | Tag String
    deriving (Show, Typeable, Data)

data Instruction = Mov Reg Reg | Ld Reg Reg | Sd Reg Reg |
    Jmp Reg | Seal Reg | SealRet Reg Reg | Call Reg Reg | Return Reg Reg | ReturnSealed Reg Reg |
    Revoke Reg | Delin Reg | Drop Reg |
    Mrev Reg Reg | Tighten Reg Reg | Li Reg Immediate | Add Reg Reg | Sub Reg Reg | Div Reg Reg |
    Mult Reg Reg |
    Le Reg Reg Reg | Eql Reg Reg Reg |
    Lt Reg Reg Reg | Jnz Reg Reg | Jz Reg Reg | Split Reg Reg Reg | Splitl Reg Reg Reg | 
    Splito Reg Reg Reg | Splitlo Reg Reg Reg | 
    Shrink Reg Reg Reg |
    Init Reg | Scc Reg Reg | Scco Reg Reg | Lcc Reg Reg |Lce Reg Reg |
    Lcb Reg Reg | Lcn Reg Reg | Out Reg | Halt | Except Reg |
    IsCap Reg Reg | And Reg Reg | Or Reg Reg
    deriving (Show, Data, Typeable)

newtype Mem = Mem (Seq MWord)
    deriving (Show)

data State = State {
    regs :: RegFile,
    mem :: Mem,
    rt :: RevTree,
    idN :: Int -- the last assigned ID
} | Error
    deriving (Show)

data Stats = Stats {
    insnCounts :: Seq Int,
    regWriteCount :: Int,
    memWriteCount :: Int,
    capOverwriteCount :: Int -- note that creating capabilities as well as destroying
            -- capabilities through other means are already included in the instruction counts
} deriving (Show)

data StateWithStats = StateWithStats State Stats


-- update stats after ovewriting a register
logWriteReg :: Stats -> RegFile -> Reg -> Stats
logWriteReg stats regs rd =
    let owc = case getReg regs rd of
                Cap _ _ _ _ _ _  -> (capOverwriteCount stats) + 1
                _ -> capOverwriteCount stats
        rwc = regWriteCount stats
    in stats { capOverwriteCount = owc, regWriteCount = rwc + 1 }

logWriteMem :: Stats -> Mem -> Int -> Stats
logWriteMem stats mem addr =
    let owc = case getMem mem addr of
                    Cap _ _ _ _ _ _  -> (capOverwriteCount stats) + 1
                    _ -> capOverwriteCount stats
        mwc = memWriteCount stats
    in stats { capOverwriteCount = owc, memWriteCount = mwc + 1 }



-- Helper functions

isValue :: MWord -> Bool
isValue (Value _) = True
isValue _ = False


isLinear :: MWord -> Bool
isLinear (Cap (TSealedRet _) b e a p n) = True
isLinear (Cap t b e a p n) = t `elem` [TLin, TRev, TSealed, TUninit]
isLinear _ = False

-- Zero out a given word if it is a linear capability
moved :: MWord -> MWord
moved w =
    if isLinear w then
        Value 0
    else
        w

getReg :: RegFile -> Reg -> MWord
getReg regs r =
    case r of
        Pc -> pc regs
        Epc -> epc regs
        Ret -> ret regs
        GPR n -> (gprs regs) `index` n

setReg :: RegFile -> Reg -> MWord -> RegFile
setReg regs r w =
    case r of
        Pc -> regs { pc = w }
        Epc -> regs { epc = w }
        Ret -> regs { ret = w }
        -- trick to replace an individual element by its index
        GPR n -> regs { gprs = Data.Sequence.update n w oldGPRs }
            where oldGPRs = gprs regs

incrementPC :: RegFile -> RegFile
incrementPC regs =
    setReg regs Pc newPC
        where 
            newPC = case oldPC of 
                Cap {} -> oldPC { capCursor = (capCursor oldPC) + 1 }
                _ -> Value 0
                where oldPC = getReg regs Pc


readableCap :: MWord -> Bool
readableCap c =
    case c of
        Cap {} -> (capPerm c) `elem` [PermR, PermRX, PermRWX] && (capType c) /= TUninit
        _ -> False

writableCap :: MWord -> Bool
writableCap c =
    case c of
        Cap {} -> (capPerm c) `elem` [PermRW, PermRWX]
        _ -> False

executableCap :: MWord -> Bool
executableCap c =
    case c of
        Cap {} -> (capPerm c) `elem` [PermRX, PermRWX] && (capType c) /= TUninit
        _ -> False 

getRevNode :: RevTree -> Int -> RevNode
getRevNode (RevTree rt) n =
    rt `index` n

setRevNode :: RevTree -> Int -> RevNode -> RevTree
setRevNode (RevTree rtl) n rn =
    RevTree $ Data.Sequence.update n rn rtl

addRevNode :: RevTree -> RevNode -> (RevTree, Int)
addRevNode (RevTree rtl) rn =
    (RevTree (rtl |> rn), Data.Sequence.length rtl)

revokedCap :: RevTree -> RevNode -> Bool
revokedCap rt rn =
    case rn of
        RevNodeRoot -> False
        RevNodeNull -> True
        RevNode n _ -> revokedCap rt parent where parent = getRevNode rt n
    

validCap :: RevTree -> MWord -> Bool
validCap rt c =
    case c of
        Cap _ _ _ _ _ rnid -> not (revokedCap rt rn) where rn = getRevNode rt rnid
        _ -> False

inBoundCap :: MWord -> Bool
inBoundCap (Cap _ b e a _ _) = b <= a && a < e

accessibleCap :: MWord -> Bool
accessibleCap (Cap t _ _ _ _ _) = t `elem` [TLin, TNon, TUninit]

getMem :: Mem -> Int -> MWord
getMem (Mem mcontent) n =
    mcontent `index` n

setMem :: Mem -> Int -> MWord -> Mem
setMem (Mem mcontent) n w =
    Mem $ Data.Sequence.update n w mcontent

permBoundedBy :: Perm -> Perm -> Bool
permBoundedBy PermNA _ = True
permBoundedBy PermR p = elem p [PermR, PermRW, PermRX, PermRWX]
permBoundedBy PermRW p = elem p [PermRW, PermRWX]
permBoundedBy PermRX p = elem p [PermRX, PermRWX]
permBoundedBy PermRWX p = elem p [PermRWX]

decodePerm :: Int -> Perm
decodePerm 0 = PermR
decodePerm 1 = PermRW
decodePerm 2 = PermRX
decodePerm 3 = PermRWX
decodePerm _ = PermNA

reparent :: RevTree -> Int -> RevNode -> RevTree
reparent (RevTree rtl) n newN =
    RevTree (mapWithIndex (\_ x -> if (x == RevNode n RNNonLin) || (x == RevNode n RNLin) then newN else x) rtl)

remove :: RevTree -> Int -> RevTree
remove rt n = setRevNode rt n RevNodeNull

updateCursor :: MWord -> MWord
updateCursor (Cap TUninit b e a p n) = Cap TUninit b e (a + 1) p n
updateCursor w = id w

getMemRange :: Mem -> Int -> Int -> Seq MWord
getMemRange (Mem meml) b s =
    Data.Sequence.take s (Data.Sequence.drop b meml)

setMemRange :: Mem -> Int -> Seq MWord -> Mem
setMemRange (Mem meml) b s =
    let l = Data.Sequence.take b meml
        r = Data.Sequence.drop (b + (Data.Sequence.length s)) meml
    in Mem (l >< s >< r)


lcxHelper :: StateWithStats -> Reg -> Reg -> (MWord -> Int) -> (StateWithStats, String)
lcxHelper (StateWithStats (State regs mem rt idN) stats) rd rs query =
    let c = getReg regs rs
        res = Value (query c)
        newRegs = setReg regs rd res
        new_stats = logWriteReg stats regs rd
    in
        if validCap rt c then
            (StateWithStats (State (incrementPC newRegs) mem rt idN) new_stats, "")
        else
            (StateWithStats Error stats, "Error lcx\n")

dSHelper :: StateWithStats -> Reg -> Reg -> (Int -> Int -> Int) -> (StateWithStats, String)
dSHelper (StateWithStats (State regs mem rt idN) stats) rd rs f =
    let n1 = getReg regs rs
        n2 = getReg regs rd
        Value v1 = n1
        Value v2 = n2
        res = Value $ f v2 v1
        newRegs = setReg regs rd res
        new_stats = logWriteReg stats regs rd
    in
        if (isValue n1) && (isValue n2) then
            (StateWithStats (State (incrementPC newRegs) mem rt idN) new_stats, "")
        else
            (StateWithStats Error stats, "Error in DS instruction\n")


rABHelper :: StateWithStats -> Reg -> Reg -> Reg -> (Int -> Int -> Int) -> (StateWithStats, String)
rABHelper (StateWithStats (State regs mem rt idN) stats) rd ra rb f =
    let na = getReg regs ra
        nb = getReg regs rb
        Value va = na
        Value vb = nb
        res = Value $ f va vb
        newRegs = setReg regs rd res
        new_stats = logWriteReg stats regs rd
    in
        if (isValue na) && (isValue nb) then
            (StateWithStats (State (incrementPC newRegs) mem rt idN) new_stats, "")
        else
            (StateWithStats (State (incrementPC (setReg regs rd $ Value 0)) mem rt idN) new_stats, "")

-- call helper (shared between call and except)
callHelper :: StateWithStats -> Reg -> MWord -> (StateWithStats, String)
callHelper (StateWithStats (State regs mem rt idN) stats) r arg =
    let ci = getReg regs r
        co = ci
        bi = capBase ci
        ei = capEnd ci
        bo = capBase co
        eo = capEnd co
        gprSize = Data.Sequence.length (gprs regs)
        newRegs = RegFile {
            pc = getMem mem bi,
            domId = getMem mem $ bi + 1,
            epc = if r == Epc then getMem mem $ bi + 2 else epc regs,
            ret = co { capType = TSealedRet r } ,  
            -- we need to give a sealedret cap for the callee to return
            gprs = Data.Sequence.update 0 arg $ getMemRange mem (bi + 4) gprSize
        }
        mem0 = setMem mem bo (pc regs)
        mem1 = setMem mem0 (bo + 1) (domId regs)
        mem2 = setMem mem1 (bo + 3) (ret regs)
        newMem = setMemRange mem2 (bo + 4) (gprs $ setReg regs r $ Value 0)
    in
        if (validCap rt ci) && (capType ci) == TSealed &&
            (validCap rt co) && (writableCap co) &&
            bi + gprSize + 4 <= ei && bo + gprSize + 4 <= eo then
            (StateWithStats (State newRegs newMem rt idN) stats, "")
        else
            (StateWithStats Error stats, "Error call: " ++ (show (ci, getMem mem bi, co)) ++ "\n")

returnHelper :: StateWithStats -> Reg -> MWord -> (StateWithStats, String)
returnHelper (StateWithStats (State regs mem rt idN) stats) r retval =
    let ci = getReg regs r
        bi = capBase ci
        ei = capEnd ci
        TSealedRet rret = capType ci
        gprSize = Data.Sequence.length (gprs regs)
        newRegs = setReg (RegFile {
            pc = getMem mem bi,
            domId = getMem mem $ bi + 1,
            epc = if r == Epc then getMem mem $ bi + 2 else epc regs,
            ret = getMem mem $ bi + 3,
            gprs = getMemRange mem (bi + 4) gprSize
        }) rret retval
    in
        if (validCap rt ci) && bi + gprSize + 4 <= ei then
            case capType ci of
                TSealedRet _ -> (StateWithStats (State newRegs mem rt idN) stats, "")
                _ -> (StateWithStats Error stats, "Error return: " ++ (show ci) ++ "\n")
        else
            (StateWithStats Error stats, "Error return: " ++ (show (ci, validCap rt ci)) ++ "\n")

-- all traps can go here
trap :: StateWithStats -> MWord -> (StateWithStats, String)
trap (StateWithStats (State regs mem rt idN) stats) arg =
    let c = epc regs
    in 
        if validCap rt c then
            callHelper (StateWithStats (State regs mem rt idN) stats) Epc arg
        else
            (StateWithStats (State regs mem rt idN) stats, "")

-- update the instruction counters
countInsn :: Stats -> Instruction -> Stats
countInsn stats insn =
    let insn_op_index = (constrIndex $ toConstr insn) - 1
        ic = insnCounts stats 
        owc = capOverwriteCount stats
        rwc = regWriteCount stats
        mwc = memWriteCount stats
        updated_ic = Data.Sequence.update insn_op_index ((ic `index` insn_op_index) + 1) ic
    in Stats updated_ic rwc mwc owc


-- Instruction definitions

execInsn :: StateWithStats -> Instruction -> (StateWithStats, String)
execInsn (StateWithStats Error stats) _ = (StateWithStats Error stats, "Error state\n")

-- mov
execInsn (StateWithStats (State regs mem rt idN) stats) (Mov rd rs) =
    (StateWithStats (State (incrementPC (setReg (setReg regs rd w) rs (moved w))) mem rt idN) new_stats, "")
    where
        w = getReg regs rs 
        new_stats = logWriteReg stats regs rd

-- ld
execInsn (StateWithStats (State regs mem rt idN) stats) (Ld rd rs) =
    let c = getReg regs rs
        w = getMem mem (capCursor c)
        new_stats = logWriteReg stats regs rd
    in
        if (validCap rt c) && (inBoundCap c) && (accessibleCap c) && (readableCap c) &&
                (not (isLinear w) || (writableCap c)) then
            (StateWithStats (State (incrementPC (setReg regs rd w)) (setMem mem (capCursor c) (moved w)) rt idN) new_stats, "")
        else
            (StateWithStats Error stats, "Error ld " ++ (show $ Ld rd rs) ++ "\n")


-- sd
execInsn (StateWithStats (State regs mem rt idN) stats) (Sd rd rs) =
    let c = getReg regs rd
        w = getReg regs rs
    in
        if (validCap rt c) && (inBoundCap c) && (accessibleCap c) && (writableCap c) then
            let newRegs = setReg (setReg regs rs (moved w)) rd (updateCursor c)
                newMem = setMem mem (capCursor c) w
                new_stats = logWriteMem stats mem (capCursor c)
            in (StateWithStats (State (incrementPC newRegs) newMem rt idN) new_stats, "")
        else
            (StateWithStats Error stats, "Error sd\n")

-- seal
execInsn (StateWithStats (State regs mem rt idN) stats) (Seal r) =
    let c = getReg regs r
        newC = c { capType = TSealed }
        newRegs = setReg regs r newC
        b = capBase c
        newIdN = idN + 1
        newMem = setMem mem (b + 1) (Value newIdN)
        new_stats = logWriteReg stats regs r
    in
        if (validCap rt c) && (readableCap c) && (writableCap c) && (capType c) == TLin then
            (StateWithStats (State (incrementPC newRegs) newMem rt newIdN) new_stats, "")
        else
            (StateWithStats Error stats, "Error seal\n")

-- sealret
execInsn (StateWithStats (State regs mem rt idN) stats) (SealRet rd rs) =
    let c = getReg regs rd
        newC = c { capType = TSealedRet rs }
        newRegs = setReg regs rd newC
        newIdN = idN + 1
        b = capBase c
        newMem = setMem mem (b + 1) (Value newIdN)
        new_stats = logWriteReg stats regs rd
    in
        if (validCap rt c) && (readableCap c) && (writableCap c) && (capType c) == TLin then
            (StateWithStats (State (incrementPC newRegs) newMem rt newIdN) new_stats, "")
        else
            (StateWithStats Error stats, "Error seal\n")
    

-- call
execInsn (StateWithStats (State regs mem rt idN) stats) (Call rd rs) =
    let arg = getReg regs rs
        new_stats = logWriteReg stats regs rs
    in callHelper (StateWithStats (State (incrementPC $ setReg regs rs $ moved arg) mem rt idN) new_stats) rd arg

-- except
execInsn (StateWithStats (State regs mem rt idN) stats) (Except r) =
    let arg = getReg regs r
    in trap (StateWithStats (State regs mem rt idN) stats) arg

-- return
execInsn (StateWithStats (State regs mem rt idN) stats) (Return rd rs) =
    let retval = getReg regs rs
    in 
        if rd == rs then
            (StateWithStats Error stats, "Error return: the two operands cannot be the same\n")
        else
            returnHelper (StateWithStats (State regs mem rt idN) stats) rd retval

-- returnsealed
execInsn (StateWithStats (State regs mem rt idN) stats) (ReturnSealed rd rs) =
    let ci = getReg regs rd
        bi = capBase ci
        ei = capEnd ci
        TSealedRet rret = capType ci
        gprSize = Data.Sequence.length (gprs regs)

        Value cursor = getReg regs rs
        newPC = (pc regs) { capCursor = cursor }
        scCap = ci
        scBase = capBase scCap
        scEnd = capEnd scCap

        regsToSave = setReg regs rd $ Value 0
        mem1 = setMem mem scBase newPC
        mem2 = setMem mem1 (scBase + 1) (domId regsToSave)
        mem3 = setMem mem2 (scBase + 2) (epc regsToSave)
        newMem = setMemRange mem2 (scBase + 4) (gprs regsToSave)

        retval = scCap { capType = TSealed }

        newRegs = setReg (RegFile {
            pc = getMem mem bi,
            domId = getMem mem $ bi + 1,
            epc = if rd == Epc then getMem mem $ bi + 2 else epc regs,
            ret = getMem mem $ bi + 3,
            gprs = getMemRange mem (bi + 4) gprSize
        }) rret retval
    in
        if (validCap rt ci) && bi + gprSize + 4 <= ei && (isValue $ getReg regs rs) && (validCap rt scCap) then
            case capType ci of
                TSealedRet _ -> (StateWithStats (State newRegs newMem rt idN) stats, "")
                _ -> (StateWithStats Error stats, "Error return: " ++ (show ci) ++ "\n")
        else
            (StateWithStats Error stats, "Error returnsealed: " ++ (show (ci, validCap rt ci)) ++ "\n")

-- revoke
execInsn (StateWithStats (State regs mem rt idN) stats) (Revoke r) =
    let c = getReg regs r
        cNode = capNode c
        RevTree rtl = rt
        rtChanged = (RevNode cNode RNLin) `elem` rtl
        newC = c { capType = if rtChanged && (writableCap c) then TUninit else TLin }
        newRegs = setReg regs r newC
        newRt = reparent rt cNode RevNodeNull 
    in
        if (validCap rt c) && (capType c) == TRev then
            (StateWithStats (State (incrementPC newRegs) mem newRt idN) stats, "")
        else
            (StateWithStats Error stats, "Error revoke\n")

-- delin
execInsn (StateWithStats (State regs mem rt idN) stats) (Delin r) =
    let c = getReg regs r
        cNode = capNode c
        rnode = getRevNode rt cNode
        newRt = setRevNode rt cNode $ case rnode of
            RevNode n _ -> RevNode n RNNonLin
            _ -> rnode

    in
        if (validCap rt c) && (capType c) == TLin then
            let newC = c { capType = TNon }
                newRegs = setReg regs r newC
            in (StateWithStats (State (incrementPC newRegs) mem newRt idN) stats, "")
        else
            (StateWithStats Error stats, "Error delin\n")
                    
-- drop
execInsn (StateWithStats (State regs mem rt idN) stats) (Drop r) =
    let c = getReg regs r
        cNode = capNode c
        parentNode = getRevNode rt cNode
    in
        if (validCap rt c) && ((capType c) `elem` [TLin, TRev, TSealed, TUninit]) then
            -- uninitialised capabilities to be dropped
            let newRt = remove (reparent rt cNode parentNode) cNode
                newRegs = setReg regs r (Value 0)
                new_stats = logWriteReg stats regs r
            in (StateWithStats (State (incrementPC newRegs) mem newRt idN) new_stats, "")
        else
            (StateWithStats (State (incrementPC regs) mem rt idN) stats, "") -- never fails

-- mrev
execInsn (StateWithStats (State regs mem rt idN) stats) (Mrev rd rs) =
    let c = getReg regs rs
        cNode = capNode c
        parentNode = getRevNode rt cNode
        (rt0, newNode) = addRevNode rt parentNode
        newRt = setRevNode rt0 cNode (RevNode newNode RNLin)
        newC = c { capType = TRev, capNode = newNode }
        newRegs = setReg regs rd newC
        new_stats = logWriteReg stats regs rd
    in
        if (validCap rt c) && (capType c) == TLin then
            (StateWithStats (State (incrementPC newRegs) mem newRt idN) new_stats, "")
        else
            (StateWithStats Error stats, "Error mrev" ++ (show (rd, c)) ++ "\n")

-- tighten
execInsn (StateWithStats (State regs mem rt idN) stats) (Tighten rd rs) =
    let c = getReg regs rd
        n = getReg regs rs
        perm = case n of
            Value v -> decodePerm v
            _ -> PermNA
    in
        if (validCap rt c) && (permBoundedBy perm (capPerm c)) then
            let newC = c { capPerm = perm }
                newRegs = setReg regs rd newC
            in (StateWithStats (State (incrementPC newRegs) mem rt idN) stats, "")
        else
            (StateWithStats Error stats, "Error tighten\n")

-- splitl
execInsn (StateWithStats (State regs mem rt idN) stats) (Splitl rd rs rp) =
    let c = getReg regs rs
        pn = getReg regs rp
        Value p = pn
        cNode = capNode c
        parentNode = getRevNode rt cNode
        (newRt, newNode) = addRevNode rt parentNode
        b = capBase c
        e = capEnd c
        c2 = c {
            capEnd = p
        }
        c1 = c {
            capBase = p,
            capNode = newNode
        }
        newRegs = setReg (setReg regs rd c1) rs c2
        new_stats = logWriteReg stats regs rd
    in
        if (validCap rt c) && (capType c) == TLin && (isValue pn) &&
            b <= p && p <= e then
            (StateWithStats (State (incrementPC newRegs) mem newRt idN) new_stats, "")
        else
            (StateWithStats Error stats, "Error splitl: " ++ (show (rd, rs, rp)) ++ "\n")



-- splitlo
execInsn (StateWithStats (State regs mem rt idN) stats) (Splitlo rd rs rp) =
    let c = getReg regs rs
        pn = getReg regs rp
        Value p = pn
        cNode = capNode c
        parentNode = getRevNode rt cNode
        (newRt, newNode) = addRevNode rt parentNode
        b = capBase c
        e = capEnd c
        c2 = c {
            capEnd = b + p
        }
        c1 = c {
            capBase = b + p,
            capNode = newNode
        }
        newRegs = setReg (setReg regs rd c1) rs c2
        new_stats = logWriteReg stats regs rd
    in
        if (validCap rt c) && (capType c) == TLin && (isValue pn) &&
            b <= b + p && b + p <= e then
            (StateWithStats (State (incrementPC newRegs) mem newRt idN) new_stats, "")
        else
            (StateWithStats Error stats, "Error splitl: " ++ (show (rd, rs, rp)) ++ "\n")

-- split
execInsn (StateWithStats (State regs mem rt idN) stats) (Split rd rs rp) =
    let c = getReg regs rs
        pn = getReg regs rp
        Value p = pn
        cNode = capNode c
        parentNode = getRevNode rt cNode
        (newRt, newNode) = addRevNode rt parentNode
        b = capBase c
        e = capEnd c
        c1 = c {
            capEnd = p
        }
        c2 = c {
            capBase = p,
            capNode = newNode
        }
        newRegs = setReg (setReg regs rd c1) rs c2
        new_stats = logWriteReg stats regs rd
    in
        if (validCap rt c) && (capType c) == TLin && (isValue pn) &&
            b <= p && p <= e then
            (StateWithStats (State (incrementPC newRegs) mem newRt idN) new_stats, "")
        else
            (StateWithStats Error stats, "Error split\n")

-- shrink
execInsn (StateWithStats (State regs mem rt idN) stats) (Shrink rd rb re) = 
    let c = getReg regs rd
        b = getReg regs rb
        e = getReg regs re
    in
        if (validCap rt c) then
            case (b, e) of
                (Value bn, Value en) ->
                    if bn >= (capBase c) && bn < en && en <= (capEnd c) then
                        let newC = c { capBase = bn, capEnd = en }
                            newRegs = setReg regs rd newC
                        in (StateWithStats (State (incrementPC newRegs) mem rt idN) stats, "")
                    else
                        (StateWithStats Error stats, "Error shrink\n")
                _ -> (StateWithStats Error stats, "Error shrink\n")
        else
            (StateWithStats Error stats, "Error shrink\n")



-- init
execInsn (StateWithStats (State regs mem rt idN) stats) (Init r) = 
    let c = getReg regs r
    in
        if (validCap rt c) && (capType c) == TUninit && (capBase c) == (capEnd c) then
            (StateWithStats (State (incrementPC (setReg regs r (c { capType = TLin }))) mem rt idN) stats, "")
        else
            (StateWithStats Error stats, "Error init\n")

-- li
execInsn (StateWithStats (State regs mem rt idN) stats) (Li r (Integer n)) =
    let newRegs = setReg regs r (Value n) 
        new_stats = logWriteReg stats regs r
    in (StateWithStats (State (incrementPC newRegs) mem rt idN) new_stats, "")



-- jmp
execInsn (StateWithStats (State regs mem rt idN) stats) (Jmp r) =
    let n = getReg regs r
        Value v = n
        curPc = getReg regs Pc
        newPc = curPc { capCursor = (capCursor curPc) + v }
        newRegs = setReg regs Pc newPc
    in
        if (isValue n) && (validCap rt curPc) then
            (StateWithStats (State newRegs mem rt idN) stats, "")
        else
            (StateWithStats Error stats, "Error jmp\n")


-- jz
execInsn (StateWithStats (State regs mem rt idN) stats) (Jz rd rs) =
    let ns = getReg regs rs
        nd = getReg regs rd
        Value vs = ns
        Value vd = nd
        curPc = getReg regs Pc
        newPc = curPc { capCursor = (capCursor curPc) + vd }
        newRegs = if vs /= 0 then
                incrementPC regs
            else
                setReg regs Pc newPc
    in
        if (isValue ns) && (isValue nd) && (validCap rt curPc) then
            (StateWithStats (State newRegs mem rt idN) stats, "")
        else
            (StateWithStats Error stats, "Error jz\n")


-- jnz
execInsn (StateWithStats (State regs mem rt idN) stats) (Jnz rd rs) =
    let ns = getReg regs rs
        nd = getReg regs rd
        Value vs = ns
        Value vd = nd
        curPc = getReg regs Pc
        newPc = curPc { capCursor = (capCursor curPc) + vd }
        newRegs = if vs == 0 then
                incrementPC regs
            else
                setReg regs Pc newPc
    in
        if (isValue ns) && (isValue nd) && (validCap rt curPc) then
            (StateWithStats (State newRegs mem rt idN) stats, "")
        else
            (StateWithStats Error stats, "Error jnz\n")

-- eq
execInsn st (Eql rd ra rb) =
    rABHelper st rd ra rb (\a b -> if a == b then 1 else 0)

-- le
execInsn st (Le rd ra rb) =
    rABHelper st rd ra rb (\a b -> if a <= b then 1 else 0)


-- lt
execInsn st (Lt rd ra rb) =
    rABHelper st rd ra rb (\a b -> if a < b then 1 else 0)


-- add
execInsn st (Add rd rs) =
    dSHelper st rd rs (\a b -> a + b)

-- div
execInsn st (Div rd rs) =
    dSHelper st rd rs (\a b -> a `div` b)

-- sub
execInsn st (Sub rd rs) =
    dSHelper st rd rs (\a b -> a - b)

-- mult
execInsn st (Mult rd rs) =
    dSHelper st rd rs (\a b -> a * b)

-- and
execInsn st (And rd rs) =
    dSHelper st rd rs (\a b -> a .&. b)

-- or
execInsn st (Or rd rs) =
    dSHelper st rd rs (\a b -> a .|. b)

-- lce
execInsn st (Lce rd rs) =
    lcxHelper st rd rs capEnd

-- lcn
execInsn st (Lcn rd rs) =
    lcxHelper st rd rs (\c -> (capEnd c) - (capBase c))

-- lcb
execInsn st (Lcb rd rs) =
    lcxHelper st rd rs capBase

-- lcc
execInsn st (Lcc rd rs) =
    lcxHelper st rd rs capCursor

-- scc
execInsn (StateWithStats (State regs mem rt idN) stats) (Scc rd rs) =
    let c = getReg regs rd
        n = getReg regs rs
        cType = capType c
        Value v = n
        newC = c { capCursor = v }
        newRegs = setReg regs rd newC
    in
        if (validCap rt c) && (isValue n) && (cType `elem` [TLin, TNon]) then
            (StateWithStats (State (incrementPC newRegs) mem rt idN) stats, "")
        else
            (StateWithStats Error stats, "Error scc\n")

-- scco
execInsn (StateWithStats (State regs mem rt idN) stats) (Scco rd rs) =
    let c = getReg regs rd
        n = getReg regs rs
        cType = capType c
        Value v = n
        newC = c { capCursor = v + (capBase c) }
        newRegs = setReg regs rd newC
    in
        if (validCap rt c) && (isValue n) && (cType `elem` [TLin, TNon]) then
            (StateWithStats (State (incrementPC newRegs) mem rt idN) stats, "")
        else
            (StateWithStats Error stats, "Error scco " ++ (show (rd, rs)) ++ "\n")

-- out
execInsn (StateWithStats (State regs mem rt idN) stats) (Out r) =
    let d = getReg regs r
    in (StateWithStats (State (incrementPC regs) mem rt idN) stats, (show r) ++ " = " ++ (show d) ++ "\n")

-- iscap
execInsn (StateWithStats (State regs mem rt idN) stats) (IsCap rd rs) =
    let c = getReg regs rs
        res = if validCap rt c then 1 else 0
        newRegs = setReg regs rd $ Value res
        new_stats = logWriteReg stats regs rd
    in
        (StateWithStats (State (incrementPC newRegs) mem rt idN) new_stats, "")

-- halt
execInsn (StateWithStats (State regs mem rt idN) stats) Halt = (StateWithStats Error stats, "halted\n")

execute :: StateWithStats -> (StateWithStats, String)
execute (StateWithStats Error stats) = (StateWithStats Error stats, "Error state\n")
execute (StateWithStats (State regs mem rt idN) stats) =
    let pcCap = getReg regs Pc
    in
        if (validCap rt pcCap) && (executableCap pcCap) && (inBoundCap pcCap) then
            let w = getMem mem (capCursor pcCap)
            in
                case w of
                    Inst insn -> let (StateWithStats s new_stats, str) = execInsn (StateWithStats (State regs mem rt idN) stats) insn
                                     sts = countInsn new_stats insn in
                          (StateWithStats s sts, str)
                    _ -> (StateWithStats Error stats, "Invalid instruction @ " ++ (show pcCap) ++ ": " ++ (show w) ++ "\n")
        else
            (StateWithStats Error stats, "Invalid PC capability: " ++ (show pcCap) ++ "\n")


-- IO

getSignificantLine :: IO String
getSignificantLine =
    let line = getLine
    in line >>= (\x -> case x of
        "" -> getSignificantLine
        '#' : _ -> getSignificantLine
        _ -> return x)


readInt :: IO Int
readInt =
    getSignificantLine >>= (\x -> return (read x :: Int))

readInts :: IO [Int]
readInts =
    getSignificantLine >>= (return . (map (\x -> (read x :: Int))) . words)

-- Format: 
-- size of memory, number of GPRs, init program counter, number of segments
-- For each segment:
-- starting address, size (number of words)
-- list of words
-- each word can be a value or an instruction (caps are not loaded)

stringToReg :: String -> Reg
stringToReg s =
    case s of
        "pc" -> Pc
        "ret" -> Ret
        "epc" -> Epc
        _ -> GPR (read (tail s) :: Int)


immediateFromStr :: String -> Immediate
immediateFromStr s =
   case s of
        '*':_ -> Tag $ s
        ':':_ -> Tag $ s
        _ -> Integer (read s :: Int)

loadWordAt :: Int -> Int -> Mem -> (Map String Int) -> IO (Mem, (Map String Int))
loadWordAt addr nwords mem tagMap = do
    if nwords == 0 then
        return (mem, tagMap)
    else do
        line <- getSignificantLine
        if (head line) == ':' then do
            tokens <- return (words line)
            loadWordAt addr nwords mem (Map.insert (tokens !! 0) addr tagMap)
        else if (head line) == '$' then
            return (mem, tagMap)
        else do
            w <- if isDigit (head line) then do
                -- data
                return (Value (read line :: Int))
            else do
                -- instruction
                tokens <- return (words line)
                r1 <- return (stringToReg (tokens !! 1))
                r2 <- return (stringToReg (tokens !! 2))
                r3 <- return (stringToReg (tokens !! 3))
                v <- return (immediateFromStr (tokens !! 2))
                return (Inst (
                    case (head tokens) of
                        "mov" -> Mov r1 r2
                        "ld" -> Ld r1 r2
                        "sd" -> Sd r1 r2
                        "seal" -> Seal r1
                        "sealret" -> SealRet r1 r2
                        "call" -> Call r1 r2
                        "ret" -> Return r1 r2
                        "retsl" -> ReturnSealed r1 r2
                        "revoke" -> Revoke r1
                        "delin" -> Delin r1
                        "drop" -> Drop r1
                        "mrev" -> Mrev r1 r2
                        "tighten" -> Tighten r1 r2
                        "split" -> Split r1 r2 r3
                        "splitl" -> Splitl r1 r2 r3
                        "splitlo" -> Splitlo r1 r2 r3
                        "splito" -> Splito r1 r2 r3
                        "shrink" -> Shrink r1 r2 r3
                        "init" -> Init r1
                        "li" -> Li r1 v
                        "add" -> Add r1 r2
                        "mult" -> Mult r1 r2
                        "div" -> Div r1 r2
                        "sub" -> Sub r1 r2
                        "and" -> And r1 r2
                        "or" -> Or r1 r2
                        "lt" -> Lt r1 r2 r3
                        "le" -> Le r1 r2 r3
                        "eq" -> Eql r1 r2 r3
                        "jnz" -> Jnz r1 r2
                        "jz" -> Jz r1 r2
                        "jmp" -> Jmp r1
                        "scc" -> Scc r1 r2
                        "scco" -> Scco r1 r2
                        "lcc" -> Lcc r1 r2
                        "lce" -> Lce r1 r2
                        "lcb" -> Lcb r1 r2
                        "lcn" -> Lcn r1 r2
                        "except" -> Except r1
                        "out" -> Out r1
                        "iscap" -> IsCap r1 r2
                        "halt" -> Halt
                        _ -> Mov Pc Pc
                    ))
            memLoaded <- return (setMem mem addr w) 
            loadWordAt (addr + 1) (nwords - 1) memLoaded tagMap

loadMemory :: Int -> Mem -> Map String Int -> IO (Mem, Map String Int)
loadMemory nsegs mem tagMap = do
    if nsegs == 0 then do
        return (mem, tagMap)
    else do
        inputs <- readInts
        startAddr <- return (inputs !! 0)
        segSize <- return (inputs !! 1)
        if startAddr < 0 then
            return (mem, tagMap)
        else do
            (memLoaded, newTagMap) <- loadWordAt startAddr segSize mem tagMap
            loadMemory (nsegs - 1) memLoaded newTagMap
    
resolveTags :: Mem -> Map String Int -> Mem
resolveTags (Mem mem) tagMap =
    Mem (mapWithIndex (\_ (addr, x) -> case x of
       Inst (Li reg (Tag ('*':tag))) -> 
           case Map.lookup tag tagMap of
               Just n -> Inst (Li reg (Integer $ n - addr - 1))
               Nothing -> Inst (Li reg (Integer 0))
       Inst (Li reg (Tag tag)) ->
           case Map.lookup tag tagMap of
               Just n -> Inst (Li reg (Integer n))
               Nothing -> Inst (Li reg (Integer 0))
       _ -> x) (Data.Sequence.zip (Data.Sequence.fromList [0..(Data.Sequence.length mem)]) mem))

type CapBound = (Immediate, Immediate, Immediate)
loadCaps :: Int -> IO (Seq CapBound)
loadCaps numCaps =
    if numCaps == 0 then
        return Empty
    else do
        line <- getSignificantLine
        immediates <- return (map (\w -> (immediateFromStr w)) (words line))
        moreCaps <- loadCaps $ numCaps - 1
        return ((immediates !! 0, immediates !! 1, immediates !! 2) <| moreCaps)

intFromImmediate :: Immediate -> Map String Int -> Int
intFromImmediate imm tagMap = 
    case imm of
        Integer i -> i
        Tag tag ->
            case Map.lookup tag tagMap of
                Just n -> n
                Nothing -> 0

loadState :: IO (State, Int)
loadState = do
    -- ugly
    inputs <- readInts
    memSize <- return (inputs !! 0)
    gprCount <- return (inputs !! 1)
    clockInterval <- return (inputs !! 2)
    numCaps <- return (inputs !! 3)
    numSegs <- return (inputs !! 4)
    capBounds <- loadCaps $ numCaps + 1
    (mem, tagMap) <- loadMemory numSegs (Mem (Data.Sequence.replicate memSize (Value 0))) Map.empty
    caps <- return (mapWithIndex (\_ (idx, (base_imm, end_imm, cursor_imm)) ->
        let base = intFromImmediate base_imm tagMap
            end = intFromImmediate end_imm tagMap
            cursor = intFromImmediate cursor_imm tagMap
        in
            Cap {
                capType = TLin,
                capBase = base,
                capEnd = end,
                capCursor = cursor,
                capPerm = PermRWX,
                capNode = idx
            } 
        ) (Data.Sequence.zip (Data.Sequence.fromList [0..(Data.Sequence.length capBounds)]) capBounds))
    capPC <- return $ caps `index` 0
    regs <- return (RegFile {
        pc = capPC,
        domId = Value 0,
        epc = Value 0,
        ret = Value 0,
        gprs = (Data.Sequence.drop 1 caps) <> (Data.Sequence.replicate (gprCount - numCaps) (Value 0))
    })
    let rt = RevTree $ Data.Sequence.replicate (numCaps + 1) RevNodeRoot
    return (State regs (resolveTags mem tagMap) rt 0, clockInterval)

execLoop :: Int -> Int -> StateWithStats -> IO Stats
execLoop _ _ (StateWithStats Error stats) = return stats
execLoop timestamp clockInterval (StateWithStats st stats) = do
    let (newStateWithStats, msg) = if (clockInterval > 0) && (mod timestamp clockInterval == 0) then
            let (StateWithStats new_st new_stats, str) = trap (StateWithStats st stats) (Value 0) in (StateWithStats new_st new_stats, str) -- 0 for timer interrupt
        else 
            execute (StateWithStats st stats)
    putStr (if msg == "" then "" else (show timestamp) ++ ": " ++ msg)
    execLoop (timestamp + 1) clockInterval newStateWithStats

printStats :: Stats -> IO ()
printStats (Stats ic rwc mwc owc) = do
    putStrLn "Instruction counts: "
    foldMap (\(n, c) -> putStrLn ((show n) ++ "\t\t\t" ++ (show c))) (Prelude.zip (dataTypeConstrs $ dataTypeOf Halt) $ Data.Foldable.toList ic)
    putStrLn $ "Register write count: " ++ (show rwc)
    putStrLn $ "Memory write count: " ++ (show mwc)
    putStrLn $ "Capability overwrite count: " ++ (show owc)

main :: IO ()

main = do
    (state, clockInterval) <- loadState
    stats <- execLoop 1 clockInterval (StateWithStats state (Stats (Data.Sequence.replicate (maxConstrIndex $ dataTypeOf Halt) 0) 0 0 0))
    putStrLn "************** Stats **************"
    printStats stats


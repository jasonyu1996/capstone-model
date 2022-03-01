import Data.Char
import Data.Map (Map)
import Data.Bits
import qualified Data.Map as Map

data CapType = TLin | TNon | TRev | TSealed | TSealedRet Reg | TUninit 
    deriving (Eq, Show)

type Addr = Int

data Perm = PermNA | PermR | PermRW | PermRX | PermRWX
    deriving (Eq, Show)

data Reg = Pc | Sc | Epc | Ret | GPR Int
    deriving (Eq, Show)

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
    sc :: MWord,
    epc :: MWord,
    ret :: MWord,
    gprs :: [MWord]
} deriving (Show)

data RevNode = RevNode Int | RevNodeRoot | RevNodeNull
    deriving (Show, Eq)

newtype RevTree = RevTree [RevNode]
    deriving (Show)

data Immediate = Integer Int | Tag String
    deriving (Show)

data Instruction = Mov Reg Reg | Ld Reg Reg | Sd Reg Reg |
    Jmp Reg | Seal Reg | SealRet Reg Reg | Call Reg Reg | Return Reg Reg | ReturnSealed Reg Reg |
    Lin Reg | Delin Reg | Drop Reg |
    Mrev Reg Reg | Tighten Reg Reg | Li Reg Immediate | Add Reg Reg | Sub Reg Reg |
    Le Reg Reg Reg | Eql Reg Reg Reg |
    Lt Reg Reg Reg | Jnz Reg Reg | Jz Reg Reg | Split Reg Reg Reg | Splitl Reg Reg Reg | 
    Splito Reg Reg Reg | Splitlo Reg Reg Reg | 
    Shrink Reg Reg Reg |
    Init Reg | Scc Reg Reg | Lcc Reg Reg | Out Reg | Halt | Except Reg |
    Scco Reg Reg | -- offset variant of scc
    IsCap Reg Reg | And Reg Reg | Or Reg Reg
    deriving (Show)

newtype Mem = Mem [MWord]
    deriving (Show)

data State = State {
    regs :: RegFile,
    mem :: Mem,
    rt :: RevTree,
    idN :: Int -- the last assigned ID
} | Error
    deriving (Show)

-- Helper functions

isValue :: MWord -> Bool
isValue (Value _) = True
isValue _ = False


-- Zero out a given word if it is a linear capability
moved :: MWord -> MWord
moved w =
    case w of
        Cap t b e a p n -> 
            case t of
                TSealedRet _ -> Value 0
                _ -> 
                    if (t `elem` [TLin, TRev, TSealed, TUninit]) then
                        Value 0
                    else
                        w
        _ -> w

getReg :: RegFile -> Reg -> MWord
getReg regs r =
    case r of
        Pc -> pc regs
        Sc -> sc regs
        Epc -> epc regs
        Ret -> ret regs
        GPR n -> (gprs regs) !! n

setReg :: RegFile -> Reg -> MWord -> RegFile
setReg regs r w =
    case r of
        Pc -> regs { pc = w }
        Sc -> regs { sc = w }
        Epc -> regs { epc = w }
        Ret -> regs { ret = w }
        -- trick to replace an individual element by its index
        GPR n -> regs { gprs = (take n oldGPRs) ++ [w] ++ (drop (n + 1) oldGPRs) }
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
    rt !! n

setRevNode :: RevTree -> Int -> RevNode -> RevTree
setRevNode (RevTree rtl) n rn =
    RevTree ((take n rtl) ++ [rn] ++ (drop (n + 1) rtl))

addRevNode :: RevTree -> RevNode -> (RevTree, Int)
addRevNode (RevTree rtl) rn =
    (RevTree (rtl ++ [rn]), length rtl)

revokedCap :: RevTree -> RevNode -> Bool
revokedCap rt rn =
    case rn of
        RevNodeRoot -> False
        RevNodeNull -> True
        RevNode n -> revokedCap rt parent where parent = getRevNode rt n
    

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
    mcontent !! n

setMem :: Mem -> Int -> MWord -> Mem
setMem (Mem mcontent) n w =
    Mem ((take n mcontent) ++ [w] ++ (drop (n + 1) mcontent))

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

reparent :: RevTree -> RevNode -> RevNode -> RevTree
reparent (RevTree rtl) n newN =
    RevTree (map (\x -> if x == n then newN else x) rtl)

remove :: RevTree -> Int -> RevTree
remove rt n = setRevNode rt n RevNodeNull

updateCursor :: MWord -> MWord
updateCursor (Cap TUninit b e a p n) = Cap TUninit b e (a + 1) p n
updateCursor w = id w

getMemRange :: Mem -> Int -> Int -> [MWord]
getMemRange (Mem meml) b s =
    take s (drop b meml)

setMemRange :: Mem -> Int -> [MWord] -> Mem
setMemRange (Mem meml) b s =
    let l = take b meml
        r = drop (b + (length s)) meml
    in Mem (l ++ s ++ r)


dSHelper :: State -> Reg -> Reg -> (Int -> Int -> Int) -> (State, String)
dSHelper (State regs mem rt idN) rd rs f =
    let n1 = getReg regs rs
        n2 = getReg regs rd
        Value v1 = n1
        Value v2 = n2
        res = Value $ f v2 v1
        newRegs = setReg regs rd res
    in
        if (isValue n1) && (isValue n2) then
            (State (incrementPC newRegs) mem rt idN, "")
        else
            (Error, "Error in DS instruction\n")


rABHelper :: State -> Reg -> Reg -> Reg -> (Int -> Int -> Int) -> (State, String)
rABHelper (State regs mem rt idN) rd ra rb f =
    let na = getReg regs ra
        nb = getReg regs rb
        Value va = na
        Value vb = nb
        res = Value $ f va vb
        newRegs = setReg regs rd res
    in
        if (isValue na) && (isValue nb) then
            (State (incrementPC newRegs) mem rt idN, "")
        else
            (Error, "Error in RAB instruction\n")

-- call helper (shared between call and except)
-- layout of sc region: bo = pc, bo + 1 = id, bo + 2 = epc, bo + 3 = ret, bo + 4 = gprs
-- upon call: load sc from mem, store ret to sc
callHelper :: State -> Reg -> MWord -> (State, String)
callHelper (State regs mem rt idN) r arg =
    let ci = getReg regs r
        co = getReg regs Sc  -- sc is not necessarily a sealed capability
        bi = capBase ci
        ei = capEnd ci
        bo = capBase co
        eo = capEnd co
        gprSize = length (gprs regs)
        newRegs = RegFile {
            pc = getMem mem bi,
            sc = ci { capType = TLin },
            domId = getMem mem $ bi + 1,
            epc = getMem mem $ bi + 2,
            ret = co { capType = TSealedRet r } ,  -- we do not load the ret from the sc region upon call
            -- we need to give a sealedret cap for the callee to return
            gprs = arg:(tail (getMemRange mem (bi + 4) gprSize))
        }
        mem0 = setMem mem bo (pc regs)
        mem1 = setMem mem0 (bo + 1) (domId regs)
        mem2 = setMem mem1 (bo + 2) (epc regs)
        mem3 = setMem mem2 (bo + 3) (ret regs)
        newMem = setMemRange mem3 (bo + 4) (gprs regs)
    in
        if (validCap rt ci) && (capType ci) == TSealed &&
            (validCap rt co) && (writableCap co) &&
            bi + gprSize + 4 <= ei && bo + gprSize + 4 <= eo then
            (State newRegs newMem rt idN, "")
        else
            (Error, "Error call: " ++ (show (ci, getMem mem bi)) ++ "\n")

returnHelper :: State -> Reg -> MWord -> (State, String)
returnHelper (State regs mem rt idN) r retval =
    let ci = getReg regs r
        bi = capBase ci
        ei = capEnd ci
        TSealedRet rret = capType ci
        gprSize = length (gprs regs)
        newRegs = setReg (RegFile {
            pc = getMem mem bi,
            sc = ci { capType = TLin },
            domId = getMem mem $ bi + 1,
            epc = getMem mem $ bi + 2,
            ret = getMem mem $ bi + 3,
            gprs = getMemRange mem (bi + 4) gprSize
        }) rret retval
        newMem = setMemRange mem bi (replicate (4 + gprSize) (Value 0)) -- clear sc to maintain linearity
    in
        if (validCap rt ci) && bi + gprSize + 4 <= ei then
            case capType ci of
                TSealedRet _ -> (State newRegs mem rt idN, "")
                _ -> (Error, "Error return: " ++ (show ci) ++ "\n")
        else
            (Error, "Error return: " ++ (show ci) ++ "\n")

-- all traps can go here
trap :: State -> MWord -> (State, String)
trap (State regs mem rt idN) arg =
    let c = epc regs
    in 
        if validCap rt c then
            callHelper (State regs mem rt idN) Epc arg
        else
            (State regs mem rt idN, "")

-- Instruction definitions

execInsn :: State -> Instruction -> (State, String)
execInsn Error _ = (Error, "Error state\n")

-- mov
execInsn (State regs mem rt idN) (Mov rd rs) =
    (State (incrementPC (setReg (setReg regs rd w) rs (moved w))) mem rt idN, "")
    where
        w = getReg regs rs 

-- ld
execInsn (State regs mem rt idN) (Ld rd rs) =
    let c = getReg regs rs
        w = getMem mem (capCursor c)
    in
        if (validCap rt c) && (inBoundCap c) && (accessibleCap c) && (readableCap c) then
            (State (incrementPC (setReg regs rd w)) (setMem mem (capCursor c) (moved w)) rt idN, "")
        else
            (Error, "Error ld " ++ (show $ Ld rd rs) ++ "\n")


-- sd
execInsn (State regs mem rt idN) (Sd rd rs) =
    let c = getReg regs rd
        w = getReg regs rs
    in
        if (validCap rt c) && (inBoundCap c) && (accessibleCap c) && (writableCap c) then
            let newRegs = setReg (setReg regs rs (moved w)) rd (updateCursor c)
                newMem = setMem mem (capCursor c) w
            in (State (incrementPC newRegs) newMem rt idN, "")
        else
            (Error, "Error sd\n")

-- seal
execInsn (State regs mem rt idN) (Seal r) =
    let c = getReg regs r
        newC = c { capType = TSealed }
        newRegs = setReg regs r newC
        b = capBase c
        newIdN = idN + 1
        newMem = setMem mem (b + 1) (Value newIdN)
    in
        if (validCap rt c) && (readableCap c) && (writableCap c) && (capType c) == TLin then
            (State (incrementPC newRegs) newMem rt newIdN, "")
        else
            (Error, "Error seal\n")

-- sealret
execInsn (State regs mem rt idN) (SealRet rd rs) =
    let c = getReg regs rd
        newC = c { capType = TSealedRet rs }
        newRegs = setReg regs rd newC
        newIdN = idN + 1
        b = capBase c
        newMem = setMem mem (b + 1) (Value newIdN)
    in
        if (validCap rt c) && (readableCap c) && (writableCap c) && (capType c) == TLin then
            (State (incrementPC newRegs) newMem rt newIdN, "")
        else
            (Error, "Error seal\n")
    

-- call
execInsn (State regs mem rt idN) (Call rd rs) =
    let arg = getReg regs rs
    in callHelper (State (incrementPC regs) mem rt idN) rd arg

-- except
execInsn (State regs mem rt idN) (Except r) =
    let arg = getReg regs r
    in trap (State regs mem rt idN) arg

-- return
execInsn (State regs mem rt idN) (Return rd rs) =
    let retval = getReg regs rs
    in 
        if rd == rs then
            (Error, "Error return: the two operands cannot be the same\n")
        else
            returnHelper (State regs mem rt idN) rd retval

-- returnsealed
execInsn (State regs mem rt idN) (ReturnSealed rd rs) =
    let Value cursor = getReg regs rs
        newPC = (pc regs) { capCursor = cursor }
        scCap = sc regs
        scBase = capBase scCap
        scEnd = capEnd scCap
        gprSize = length $ gprs regs

        mem1 = setMem mem scBase newPC
        mem2 = setMem mem1 (scBase + 1) (domId regs)
        mem3 = setMem mem2 (scBase + 2) (epc regs)
        newMem = setMemRange mem2 (scBase + 4) (gprs regs)

        retval = scCap { capType = TSealed }
    in 
        if (isValue $ getReg regs rs) && (validCap rt scCap) &&
            (scBase + gprSize + 3 < scEnd) && (writableCap scCap) then
            returnHelper (State regs newMem rt idN) rd retval
        else
            (Error, "Error returnsealed\n")

-- lin
execInsn (State regs mem rt idN) (Lin r) =
    let c = getReg regs r
        cNode = capNode c
        RevTree rtl = rt
        rtChanged = (RevNode cNode) `elem` rtl
        newC = c { capType = if rtChanged then TUninit else TLin }
        newRegs = setReg regs r newC
        newRt = reparent rt (RevNode cNode) RevNodeNull
    in
        if (validCap rt c) && (capType c) == TRev then
            (State (incrementPC newRegs) mem newRt idN, "")
        else
            (Error, "Error lin\n")

-- delin
execInsn (State regs mem rt idN) (Delin r) =
    let c = getReg regs r
    in
        if (validCap rt c) && (capType c) == TLin then
            let newC = c { capType = TNon }
                newRegs = setReg regs r newC
            in (State (incrementPC newRegs) mem rt idN, "")
        else
            (Error, "Error delin\n")
                    
-- drop
execInsn (State regs mem rt idN) (Drop r) =
    let c = getReg regs r
        cNode = capNode c
        parentNode = getRevNode rt cNode
    in
        if (validCap rt c) && ((capType c) `elem` [TLin, TRev, TSealed, TUninit]) then
            let newRt = remove (reparent rt (RevNode cNode) parentNode) cNode
                newRegs = setReg regs r (Value 0)
            in (State (incrementPC newRegs) mem newRt idN, "")
        else
            (Error, "Error drop " ++ (show (r, c)) ++ "\n")

-- mrev
execInsn (State regs mem rt idN) (Mrev rd rs) =
    let c = getReg regs rs
        cNode = capNode c
        parentNode = getRevNode rt cNode
        (rt0, newNode) = addRevNode rt parentNode
        newRt = setRevNode rt0 cNode (RevNode newNode)
        newC = c { capType = TRev, capNode = newNode }
        newRegs = setReg regs rd newC
    in
        if (validCap rt c) && (capType c) == TLin then
            (State (incrementPC newRegs) mem newRt idN, "")
        else
            (Error, "Error mrev" ++ (show (rd, c)) ++ "\n")

-- tighten
execInsn (State regs mem rt idN) (Tighten rd rs) =
    let c = getReg regs rd
        n = getReg regs rs
        perm = case n of
            Value v -> decodePerm v
            _ -> PermNA
    in
        if (validCap rt c) && (permBoundedBy perm (capPerm c)) then
            let newC = c { capPerm = perm }
                newRegs = setReg regs rd newC
            in (State (incrementPC newRegs) mem rt idN, "")
        else
            (Error, "Error tighten\n")

-- splitl
execInsn (State regs mem rt idN) (Splitl rd rs rp) =
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
    in
        if (validCap rt c) && (capType c) == TLin && (isValue pn) &&
            b <= p && p <= e then
            (State (incrementPC newRegs) mem newRt idN, "")
        else
            (Error, "Error splitl: " ++ (show (rd, rs, rp)) ++ "\n")



-- splitlo
execInsn (State regs mem rt idN) (Splitlo rd rs rp) =
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
    in
        if (validCap rt c) && (capType c) == TLin && (isValue pn) &&
            b <= b + p && b + p <= e then
            (State (incrementPC newRegs) mem newRt idN, "")
        else
            (Error, "Error splitl: " ++ (show (rd, rs, rp)) ++ "\n")

-- split
execInsn (State regs mem rt idN) (Split rd rs rp) =
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
    in
        if (validCap rt c) && (capType c) == TLin && (isValue pn) &&
            b <= p && p <= e then
            (State (incrementPC newRegs) mem newRt idN, "")
        else
            (Error, "Error split\n")

-- shrink
execInsn (State regs mem rt idN) (Shrink rd rb re) = 
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
                        in (State (incrementPC newRegs) mem rt idN, "")
                    else
                        (Error, "Error shrink\n")
                _ -> (Error, "Error shrink\n")
        else
            (Error, "Error shrink\n")



-- init
execInsn (State regs mem rt idN) (Init r) = 
    let c = getReg regs r
    in
        if (validCap rt c) && (capType c) == TUninit && (capBase c) == (capEnd c) then
            (State (incrementPC (setReg regs r (c { capType = TLin }))) mem rt idN, "")
        else
            (Error, "Error init\n")

-- li
execInsn (State regs mem rt idN) (Li r (Integer n)) =
    let newRegs = setReg regs r (Value n) in (State (incrementPC newRegs) mem rt idN, "")



-- jmp
execInsn (State regs mem rt idN) (Jmp r) =
    let n = getReg regs r
        Value v = n
        curPc = getReg regs Pc
        newPc = curPc { capCursor = v }
        newRegs = setReg regs Pc newPc
    in
        if (isValue n) && (validCap rt curPc) then
            (State newRegs mem rt idN, "")
        else
            (Error, "Error jmp\n")


-- jz
execInsn (State regs mem rt idN) (Jz rd rs) =
    let ns = getReg regs rs
        nd = getReg regs rd
        Value vs = ns
        Value vd = nd
        curPc = getReg regs Pc
        newPc = curPc { capCursor = vd }
        newRegs = if vs /= 0 then
                incrementPC regs
            else
                setReg regs Pc newPc
    in
        if (isValue ns) && (isValue nd) && (validCap rt curPc) then
            (State newRegs mem rt idN, "")
        else
            (Error, "Error jnz\n")


-- jnz
execInsn (State regs mem rt idN) (Jnz rd rs) =
    let ns = getReg regs rs
        nd = getReg regs rd
        Value vs = ns
        Value vd = nd
        curPc = getReg regs Pc
        newPc = curPc { capCursor = vd }
        newRegs = if vs == 0 then
                incrementPC regs
            else
                setReg regs Pc newPc
    in
        if (isValue ns) && (isValue nd) && (validCap rt curPc) then
            (State newRegs mem rt idN, "")
        else
            (Error, "Error jnz\n")

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

-- sub
execInsn st (Sub rd rs) =
    dSHelper st rd rs (\a b -> a - b)

-- and
execInsn st (And rd rs) =
    dSHelper st rd rs (\a b -> a .&. b)

-- or
execInsn st (Or rd rs) =
    dSHelper st rd rs (\a b -> a .|. b)

-- lcc
execInsn (State regs mem rt idN) (Lcc rd rs) =
    let c = getReg regs rs
        res = Value (capCursor c)
        newRegs = setReg regs rd res
    in
        if validCap rt c then
            (State (incrementPC newRegs) mem rt idN, "")
        else
            (Error, "Error lcc\n")

-- scc
execInsn (State regs mem rt idN) (Scc rd rs) =
    let c = getReg regs rd
        n = getReg regs rs
        cType = capType c
        Value v = n
        newC = c { capCursor = v }
        newRegs = setReg regs rd newC
    in
        if (validCap rt c) && (isValue n) && (cType `elem` [TLin, TNon]) then
            (State (incrementPC newRegs) mem rt idN, "")
        else
            (Error, "Error scc\n")

-- scco
execInsn (State regs mem rt idN) (Scco rd rs) =
    let c = getReg regs rd
        n = getReg regs rs
        cType = capType c
        Value v = n
        newC = c { capCursor = v + (capBase c) }
        newRegs = setReg regs rd newC
    in
        if (validCap rt c) && (isValue n) && (cType `elem` [TLin, TNon]) then
            (State (incrementPC newRegs) mem rt idN, "")
        else
            (Error, "Error scco\n")

-- out
execInsn (State regs mem rt idN) (Out r) =
    let d = getReg regs r
    in (State (incrementPC regs) mem rt idN, (show r) ++ " = " ++ (show d) ++ "\n")

-- iscap
execInsn (State regs mem rt idN) (IsCap rd rs) =
    let c = getReg regs rs
        res = if validCap rt c then 1 else 0
        newRegs = setReg regs rd $ Value res
    in
        (State (incrementPC newRegs) mem rt idN, "")

-- halt
execInsn (State regs mem rt idN) Halt = (Error, "halted\n")

execute :: State -> (State, String)
execute Error = (Error, "Error state\n")
execute (State regs mem rt idN) =
    let pcCap = getReg regs Pc
    in
        if (validCap rt pcCap) && (executableCap pcCap) && (inBoundCap pcCap) then
            let w = getMem mem (capCursor pcCap)
            in
                case w of
                    Inst insn -> execInsn (State regs mem rt idN) insn
                    _ -> (Error, "Invalid instruction @ " ++ (show pcCap) ++ ": " ++ (show w) ++ "\n")
        else
            (Error, "Invalid PC capability: " ++ (show pcCap) ++ "\n")


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
-- TODO: init program counter with tag

stringToReg :: String -> Reg
stringToReg s =
    case s of
        "pc" -> Pc
        "ret" -> Ret
        "epc" -> Epc
        "sc" -> Sc
        _ -> GPR (read (tail s) :: Int)


immediateFromStr :: String -> Immediate
immediateFromStr s =
   case s of
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
                        "lin" -> Lin r1
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
    Mem (map (\x -> case x of
       Inst (Li reg (Tag tag)) -> case Map.lookup tag tagMap of
        Just n -> Inst (Li reg (Integer n))
        Nothing -> Inst (Li reg (Integer 0))
       _ -> x) mem)

type CapBound = (Immediate, Immediate, Immediate)
loadCaps :: Int -> IO [CapBound]
loadCaps numCaps =
    if numCaps == 0 then
        return []
    else do
        line <- getSignificantLine
        immediates <- return (map (\w -> (immediateFromStr w)) (words line))
        moreCaps <- loadCaps $ numCaps - 1
        return ((immediates !! 0, immediates !! 1, immediates !! 2):moreCaps)

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
    (mem, tagMap) <- loadMemory numSegs (Mem (replicate memSize (Value 0))) Map.empty
    caps <- return (map (\(idx, (base_imm, end_imm, cursor_imm)) ->
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
        ) (zip [0..] capBounds))
    capPC <- return $ head caps
    regs <- return (RegFile {
        pc = capPC,
        domId = Value 0,
        sc = Value 0, -- todo need to set this up
        epc = Value 0,
        ret = Value 0,
        gprs = (tail caps) ++ (replicate (gprCount - numCaps) (Value 0))
    })
    let rt = RevTree $ replicate (numCaps + 1) RevNodeRoot
    return (State regs (resolveTags mem tagMap) rt 0, clockInterval)

execLoop :: Int -> Int -> State -> IO ()
execLoop _ _ Error = return ()
execLoop timestamp clockInterval st = do
    let (newState, msg) = if (clockInterval > 0) && (mod timestamp clockInterval == 0) then
            trap st (Value 0) -- 0 for timer interrupt
        else  
            execute st
    putStr (if msg == "" then "" else (show timestamp) ++ ": " ++ msg)
    --putStrLn (show (length (gprs (regs newState))))
    --putStrLn ((show timestamp) ++ ": " ++ (show newState))
    execLoop (timestamp + 1) clockInterval newState

main :: IO ()

main = do
    (state, clockInterval) <- loadState
    --putStrLn ("Initial state: " ++ (show state))
    execLoop 1 clockInterval state 


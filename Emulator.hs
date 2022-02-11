import Data.Char

data CapType = TLin | TNon | TRev | TSealed | TUninit 
    deriving (Eq, Show)

type Addr = Int

data Perm = PermNA | PermR | PermRW | PermRX | PermRWX
    deriving (Eq, Show)

data Reg = Pc | Sc | Ret | GPR Int
    deriving (Show)

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
    sc :: MWord,
    ret :: MWord,
    gprs :: [MWord]
} deriving (Show)

data RevNode = RevNode Int | RevNodeRoot | RevNodeNull
    deriving (Show, Eq)

data RevTree = RevTree [RevNode]
    deriving (Show)

data Instruction = Mov Reg Reg | Ld Reg Reg | Sd Reg Reg |
    Jmp Reg | Seal Reg | Call Reg | Lin Reg | Delin Reg | Drop Reg |
    Mrev Reg Reg | Tighten Reg Reg | Li Reg Int | Add Reg Reg |
    Lt Reg Reg Reg | Jnz Reg Reg | Split Reg Reg Reg | Shrink Reg Reg Reg |
    Init Reg | Scc Reg Reg | Lcc Reg Reg
    deriving (Show)

data Mem = Mem [MWord]
    deriving (Show)

data State = State RegFile Mem RevTree | Error
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
            if t `elem` [TLin, TRev, TSealed, TUninit] then
                Value 0
            else
                w
        _ -> w

getReg :: RegFile -> Reg -> MWord
getReg regs r =
    case r of
        Pc -> pc regs
        Sc -> sc regs
        Ret -> ret regs
        GPR n -> (gprs regs) !! n

setReg :: RegFile -> Reg -> MWord -> RegFile
setReg regs r w =
    case r of
        Pc -> regs { pc = w }
        Sc -> regs { sc = w }
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
    take b (drop s meml)

setMemRange :: Mem -> Int -> [MWord] -> Mem
setMemRange (Mem meml) b s =
    let l = take b meml
        r = drop (b + (length s)) meml
    in Mem (l ++ s ++ r)

-- Instruction definitions

execInsn :: State -> Instruction -> State
execInsn Error _ = Error

-- mov
execInsn (State regs mem rt) (Mov rd rs) =
    State (incrementPC (setReg (setReg regs rd w) rs (moved w))) mem rt
    where
        w = getReg regs rs 

-- ld
execInsn (State regs mem rt) (Ld rd rs) =
    let c = getReg regs rs
        w = getMem mem (capCursor c)
    in
        if (validCap rt c) && (inBoundCap c) && (accessibleCap c) && (readableCap c) then
            State (incrementPC (setReg regs rd w)) (setMem mem (capCursor c) (moved w)) rt
        else
            Error


-- sd
execInsn (State regs mem rt) (Sd rd rs) =
    let c = getReg regs rd
        w = getReg regs rs
    in
        if (validCap rt c) && (inBoundCap c) && (accessibleCap c) && (writableCap c) then
            let newRegs = setReg (setReg regs rs (moved w)) rd (updateCursor c)
                newMem = setMem mem (capCursor c) w
            in State (incrementPC newRegs) newMem rt
        else
            Error

-- seal
execInsn (State regs mem rt) (Seal r) =
    let c = getReg regs r
        newC = c { capType = TSealed }
        newRegs = setReg regs r newC
    in
        if (validCap rt c) && (readableCap c) && (writableCap c) && (capType c) == TLin then
            State (incrementPC newRegs) mem rt
        else
            Error

-- call
execInsn (State regs mem rt) (Call r) =
    let ci = getReg regs r
        co = getReg regs Sc
        bi = capBase ci
        ei = capEnd ci
        bo = capBase co
        eo = capEnd co
        gprSize = length (gprs regs)
        newRegs = RegFile {
            pc = getMem mem bi,
            sc = ci,
            ret = co,
            gprs = getMemRange mem (bi + 1) gprSize
        }
        newMem = setMemRange (setMem mem bo (pc regs)) (bo + 1) (gprs regs)
    in
        if (validCap rt ci) && (capType ci) == TSealed &&
            (validCap rt co) && (capType co) == TSealed &&
            bi + gprSize < ei && bo + gprSize < eo then
            State newRegs newMem rt
        else
            Error



-- lin
execInsn (State regs mem rt) (Lin r) =
    let c = getReg regs r
        cNode = capNode c
        RevTree rtl = rt
        rtChanged = (RevNode cNode) `elem` rtl
        newC = c { capType = if rtChanged then TUninit else TLin }
        newRegs = setReg regs r newC
        newRt = reparent rt (RevNode cNode) RevNodeNull
    in
        if (validCap rt c) && (capType c) == TRev then
            State (incrementPC newRegs) mem newRt
        else
            Error

-- delin
execInsn (State regs mem rt) (Delin r) =
    let c = getReg regs r
    in
        if (validCap rt c) && (capType c) == TLin then
            let newC = c { capType = TNon }
                newRegs = setReg regs r newC
            in State (incrementPC newRegs) mem rt
        else
            Error
                    
-- drop
execInsn (State regs mem rt) (Drop r) =
    let c = getReg regs r
        cNode = capNode c
        parentNode = getRevNode rt cNode
    in
        if (validCap rt c) && ((capType c) `elem` [TLin, TRev, TSealed, TUninit]) then
            let newRt = remove (reparent rt (RevNode cNode) parentNode) cNode
                newRegs = setReg regs r (Value 0)
            in State (incrementPC newRegs) mem newRt
        else
            Error

-- mrev
execInsn (State regs mem rt) (Mrev rd rs) =
    let c = getReg regs rs
        cNode = capNode c
        parentNode = getRevNode rt cNode
        (irt, newNode) = addRevNode rt parentNode
        newRt = setRevNode irt cNode (RevNode newNode)
        newC = c { capType = TRev, capNode = newNode }
        newRegs = setReg regs rd newC
    in
        if (validCap rt c) && (capType c) == TLin then
            State (incrementPC newRegs) mem newRt
        else
            Error

-- tighten
execInsn (State regs mem rt) (Tighten rd rs) =
    let c = getReg regs rd
        n = getReg regs rs
        perm = case n of
            Value v -> decodePerm v
            _ -> PermNA
    in
        if (validCap rt c) && (permBoundedBy perm (capPerm c)) then
            let newC = c { capPerm = perm }
                newRegs = setReg regs rd newC
            in State (incrementPC newRegs) mem rt
        else
            Error


-- split
execInsn (State regs mem rt) (Split rd rs rp) =
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
            b < p && p < e then
            State (incrementPC newRegs) mem newRt
        else
            Error

-- shrink
execInsn (State regs mem rt) (Shrink rd rb re) = 
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
                        in State (incrementPC newRegs) mem rt
                    else
                        Error
                _ -> Error
        else
            Error



-- init
execInsn (State regs mem rt) (Init r) = 
    let c = getReg regs r
    in
        if (validCap rt c) && (capType c) == TUninit && (capBase c) == (capEnd c) then
            State (incrementPC (setReg regs r (c { capType = TLin }))) mem rt
        else
            Error

-- li
execInsn (State regs mem rt) (Li r n) =
    let newRegs = setReg regs r (Value n) in State (incrementPC newRegs) mem rt


-- add
execInsn (State regs mem rt) (Add rd rs) =
    let n1 = getReg regs rs
        n2 = getReg regs rd
        Value v1 = n1
        Value v2 = n2
        res = Value (v1 + v2)
        newRegs = setReg regs rd res
    in
        if (isValue n1) && (isValue n2) then
            State (incrementPC newRegs) mem rt
        else
            Error

-- jmp
execInsn (State regs mem rt) (Jmp r) =
    let n = getReg regs r
        Value v = n
        curPc = getReg regs Pc
        newPc = curPc { capCursor = v }
        newRegs = setReg regs Pc newPc
    in
        if (isValue n) && (validCap rt curPc) then
            State newRegs mem rt
        else
            Error

-- jnz
execInsn (State regs mem rt) (Jnz rd rs) =
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
            State newRegs mem rt
        else
            Error

-- lt
execInsn (State regs mem rt) (Lt rd ra rb) =
    let na = getReg regs ra
        nb = getReg regs rb
        Value va = na
        Value vb = nb
        res = Value (if va < vb then 1 else 0)
        newRegs = setReg regs rd res
    in
        if (isValue na) && (isValue nb) then
            State (incrementPC newRegs) mem rt
        else
            Error

-- lcc
execInsn (State regs mem rt) (Lcc rd rs) =
    let c = getReg regs rs
        res = Value (capCursor c)
        newRegs = setReg regs rd res
    in
        if validCap rt c then
            State (incrementPC newRegs) mem rt
        else
            Error

-- scc
execInsn (State regs mem rt) (Scc rd rs) =
    let c = getReg regs rd
        n = getReg regs rs
        cType = capType c
        Value v = n
        newC = c { capCursor = v }
        newRegs = setReg regs rd newC
    in
        if (validCap rt c) && (isValue n) && (cType `elem` [TLin, TNon]) then
            State (incrementPC newRegs) mem rt
        else
            Error


execute :: State -> State
execute Error = Error
execute (State regs mem rt) =
    let pcCap = getReg regs Pc
    in
        if (validCap rt pcCap) && (executableCap pcCap) && (inBoundCap pcCap) then
            let w = getMem mem (capCursor pcCap)
            in
                case w of
                    Inst insn -> execInsn (State regs mem rt) insn
                    _ -> Error
        else
            Error


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
        "sc" -> Sc
        _ -> GPR (read (tail s) :: Int)


loadWordAt :: Int -> Int -> Mem -> IO Mem
loadWordAt addr nwords mem = do
    if nwords <= 0 then do
        return mem
    else do
        line <- getSignificantLine
        w <- if isDigit (head line) then do
            -- data
            return (Value (read line :: Int))
        else do
            -- instruction
            tokens <- return (words line)
            r1 <- return (stringToReg (tokens !! 1))
            r2 <- return (stringToReg (tokens !! 2))
            r3 <- return (stringToReg (tokens !! 3))
            v <- return (read (tokens !! 2) :: Int)
            return (Inst (
                case (head tokens) of
                    "mov" -> Mov r1 r2
                    "ld" -> Ld r1 r2
                    "sd" -> Sd r1 r2
                    "seal" -> Seal r1
                    "call" -> Call r1
                    "lin" -> Lin r1
                    "delin" -> Delin r1
                    "drop" -> Drop r1
                    "mrev" -> Mrev r1 r2
                    "tighten" -> Tighten r1 r2
                    "split" -> Split r1 r2 r3
                    "shrink" -> Shrink r1 r2 r3
                    "init" -> Init r1
                    "li" -> Li r1 v
                    "add" -> Add r1 r2
                    "lt" -> Lt r1 r2 r3
                    "jnz" -> Jnz r1 r2
                    "jmp" -> Jmp r1
                    "scc" -> Scc r1 r2
                    "lcc" -> Lcc r1 r2
                    _ -> Mov Pc Pc
                ))
        memLoaded <- return (setMem mem addr w) 
        loadWordAt (addr + 1) (nwords - 1) memLoaded

loadMemory :: Int -> Mem -> IO Mem
loadMemory nsegs mem = do
    if nsegs <= 0 then do
        return mem
    else do
        inputs <- readInts
        startAddr <- return (inputs !! 0)
        segSize <- return (inputs !! 1)
        memLoaded <- loadWordAt startAddr segSize mem
        loadMemory (nsegs - 1) memLoaded
    
    

loadState :: IO State
loadState = do
    -- ugly
    inputs <- readInts
    memSize <- return (inputs !! 0)
    gprCount <- return (inputs !! 1)
    initPC <- return (inputs !! 2)
    numSegs <- return (inputs !! 3)
    capPC <- return (Cap {
            capType = TLin,
            capBase = 0,
            capEnd = memSize - 1,
            capCursor = initPC,
            capPerm = PermRWX,
            capNode = 0
    })
    regs <- return (RegFile {
        pc = capPC,
        sc = Value 0, -- todo need to set this up
        ret = Value 0,
        gprs = replicate gprCount (Value 0)
    })
    mem <- loadMemory numSegs (Mem (replicate memSize (Value 0)))
    let rt = RevTree [RevNodeRoot]
    return (State regs mem rt)

execLoop :: Int -> State -> IO ()
execLoop _ Error = return ()
execLoop timestamp st = do
    let newState = execute st
    putStrLn ((show timestamp) ++ ": " ++ (show newState))
    execLoop (timestamp + 1) newState

main :: IO ()

main = do
    state <- loadState
    putStrLn ("Initial state: " ++ (show state))
    execLoop 1 state


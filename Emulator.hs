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
    deriving (Show)

data RevTree = RevTree [RevNode]
    deriving (Show)

data Instruction = Mov Reg Reg | Ld Reg Reg | Sd Reg Reg |
    Jmp Reg | Seal Reg | Call Reg | Lin Reg | Delin Reg | Drop Reg |
    Mrev Reg Reg | Tighten Reg Reg | Li Reg Int | Add Reg Reg |
    Lt Reg Reg Reg | Jnz Reg Reg | Split Reg Reg Reg | Shrink Reg Reg Reg |
    Init Reg
    deriving (Show)

data Mem = Mem [MWord]
    deriving (Show)

data State = State RegFile Mem RevTree | Error
    deriving (Show)

-- Helpe functions

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
            State (incrementPC (setReg regs rs (moved w))) (setMem mem (capCursor c) w) rt
        else
            Error

-- seal
execInsn (State regs mem rt) (Seal r) = (State regs mem rt) -- TODO: unimplemented

-- call
execInsn (State regs mem rt) (Call r) = (State regs mem rt) -- TODO: unimplemented

-- lin
execInsn (State regs mem rt) (Lin r) = (State regs mem rt) -- TODO: unimplemented

-- delin
execInsn (State regs mem rt) (Delin r) = (State regs mem rt) -- TODO: unimplemented
                    
-- drop
execInsn (State regs mem rt) (Drop r) = (State regs mem rt) -- TODO: unimplemented

-- mrev
execInsn (State regs mem rt) (Mrev rd rs) = (State regs mem rt) -- TODO: unimplemented

-- tighten
execInsn (State regs mem rt) (Tighten rd rs) = (State regs mem rt) -- TODO: unimplemented

-- split
execInsn (State regs mem rt) (Split rd rs rp) = (State regs mem rt) -- TODO: unimplemented

-- shrink
execInsn (State regs mem rt) (Shrink rd rs rp) = (State regs mem rt) -- TODO: unimplemented

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


readInt :: IO (Int)
readInt = do
    getLine >>= (\x -> return (read x :: Int))

-- Format: 
-- size of memory
-- number of GPRs
-- init program counter
-- number of segments
-- For each segment:
-- starting address
-- size (number of words)
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
        line <- getLine
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
                    _ -> Mov Pc Pc
                ))
        memLoaded <- return (setMem mem addr w) 
        loadWordAt (addr + 1) (nwords - 1) memLoaded

loadMemory :: Int -> Mem -> IO Mem
loadMemory nsegs mem = do
    if nsegs <= 0 then do
        return mem
    else do
        startAddr <- readInt
        segSize <- readInt
        memLoaded <- loadWordAt startAddr segSize mem
        loadMemory (nsegs - 1) memLoaded
    
    

loadState :: IO State
loadState = do
    memSize <- readInt
    gprCount <- readInt
    initPC <- readInt
    numSegs <- readInt
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

